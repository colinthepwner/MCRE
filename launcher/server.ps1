param(
    [int]$Port = 8642,
    [switch]$Tab,
    [switch]$NoBrowser
)

$ErrorActionPreference = 'Stop'

Add-Type -Namespace McpeWeb -Name Win32 -MemberDefinition @'
[DllImport("kernel32.dll")] public static extern System.IntPtr GetConsoleWindow();
[DllImport("user32.dll")] public static extern bool ShowWindow(System.IntPtr hWnd, int nCmdShow);
'@
function Show-Console { [void][McpeWeb.Win32]::ShowWindow([McpeWeb.Win32]::GetConsoleWindow(), 5) }
function Show-Error([string]$text) {
    Add-Type -AssemblyName System.Windows.Forms
    [void][System.Windows.Forms.MessageBox]::Show($text, 'Minecraft PE', 'OK', 'Error')
}

$Root      = (Resolve-Path (Join-Path $PSScriptRoot '..')).ProviderPath
$SavesDir  = Join-Path $Root 'saves'
$TrashDir  = Join-Path $SavesDir '.trash'
$BackupDir = Join-Path $Root 'backups'
$StoreIdFile = Join-Path $SavesDir '.store-id'
$MaxBackups = 10
$AppTag = 'mcpe-web-saves'
$Url = "http://localhost:$Port/"

function Write-Info($msg)  { Write-Host $msg -ForegroundColor Gray }
function Write-Good($msg)  { Write-Host $msg -ForegroundColor Green }
function Write-Warn2($msg) { Write-Host $msg -ForegroundColor Yellow }

New-Item -ItemType Directory -Force -Path $SavesDir | Out-Null
New-Item -ItemType Directory -Force -Path $BackupDir | Out-Null

if (-not (Test-Path $StoreIdFile)) {
    [IO.File]::WriteAllText($StoreIdFile, [guid]::NewGuid().ToString())
}
$StoreId = ([IO.File]::ReadAllText($StoreIdFile)).Trim()

Add-Type -AssemblyName System.IO.Compression
Add-Type -AssemblyName System.IO.Compression.FileSystem

function Get-SaveFiles {
    if (-not (Test-Path $SavesDir)) { return @() }
    Get-ChildItem -Path $SavesDir -Recurse -File -Force | Where-Object {
        $rel = $_.FullName.Substring($SavesDir.Length + 1)
        -not ($rel -like '.trash\*') -and $rel -ne '.store-id' -and -not ($_.Name -like '*.mcsave-tmp')
    }
}

function New-SavesBackup {
    $files = @(Get-SaveFiles)
    if ($files.Count -eq 0) { return }
    $stamp = Get-Date -Format 'yyyy-MM-dd_HH-mm-ss'
    $zipPath = Join-Path $BackupDir "saves_$stamp.zip"
    try {
        $fs = [IO.File]::Open($zipPath, [IO.FileMode]::CreateNew)
        try {
            $zip = New-Object IO.Compression.ZipArchive($fs, [IO.Compression.ZipArchiveMode]::Create)
            try {
                foreach ($f in $files) {
                    $rel = $f.FullName.Substring($SavesDir.Length + 1).Replace('\', '/')
                    [IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zip, $f.FullName, $rel, [IO.Compression.CompressionLevel]::Optimal) | Out-Null
                }
            } finally { $zip.Dispose() }
        } finally { $fs.Dispose() }
        Write-Info "Backed up saves to backups\saves_$stamp.zip"
    } catch {
        Write-Warn2 "Backup failed (continuing anyway): $($_.Exception.Message)"
    }
    Get-ChildItem -Path $BackupDir -Filter 'saves_*.zip' | Sort-Object Name -Descending |
        Select-Object -Skip $MaxBackups | Remove-Item -Force -ErrorAction SilentlyContinue
}

$Mime = @{
    '.html' = 'text/html; charset=utf-8'
    '.htm'  = 'text/html; charset=utf-8'
    '.js'   = 'text/javascript; charset=utf-8'
    '.mjs'  = 'text/javascript; charset=utf-8'
    '.json' = 'application/json; charset=utf-8'
    '.wasm' = 'application/wasm'
    '.data' = 'application/octet-stream'
    '.css'  = 'text/css; charset=utf-8'
    '.png'  = 'image/png'
    '.jpg'  = 'image/jpeg'
    '.svg'  = 'image/svg+xml'
    '.ico'  = 'image/x-icon'
    '.txt'  = 'text/plain; charset=utf-8'
    '.md'   = 'text/plain; charset=utf-8'
}

$Utf8NoBom = New-Object Text.UTF8Encoding($false)
$EpochUtc = [DateTime]::SpecifyKind([DateTime]'1970-01-01', [DateTimeKind]::Utc)

function ConvertTo-UnixMs([DateTime]$dt) {
    [long][Math]::Floor(($dt.ToUniversalTime() - $EpochUtc).TotalMilliseconds)
}
function ConvertFrom-UnixMs([long]$ms) {
    $EpochUtc.AddMilliseconds($ms)
}

function Send-Bytes($ctx, [int]$status, [string]$contentType, [byte[]]$bytes) {
    $res = $ctx.Response
    $res.StatusCode = $status
    $res.ContentType = $contentType
    $res.Headers['Cache-Control'] = 'no-store'
    $res.ContentLength64 = $bytes.Length
    if ($ctx.Request.HttpMethod -ne 'HEAD' -and $bytes.Length -gt 0) {
        $res.OutputStream.Write($bytes, 0, $bytes.Length)
    }
    $res.OutputStream.Close()
}

function Send-Json($ctx, [int]$status, $obj) {
    $json = $obj | ConvertTo-Json -Depth 6 -Compress
    Send-Bytes $ctx $status 'application/json; charset=utf-8' $Utf8NoBom.GetBytes($json)
}

function Send-Text($ctx, [int]$status, [string]$text) {
    Send-Bytes $ctx $status 'text/plain; charset=utf-8' $Utf8NoBom.GetBytes($text)
}

function Read-Body($req) {
    $ms = New-Object IO.MemoryStream
    try { $req.InputStream.CopyTo($ms); return ,$ms.ToArray() } finally { $ms.Dispose(); $req.InputStream.Close() }
}

function Resolve-SavePath([string]$rel) {
    if ([string]::IsNullOrWhiteSpace($rel)) { return $null }
    $parts = @($rel.Replace('\', '/').Split('/') | Where-Object { $_ -ne '' })
    if ($parts.Count -eq 0) { return $null }
    foreach ($p in $parts) {
        if ($p -eq '.' -or $p -eq '..') { return $null }
        if ($p.IndexOfAny([IO.Path]::GetInvalidFileNameChars()) -ge 0) { return $null }
    }
    if ($parts[0] -eq '.trash' -or ($parts.Count -eq 1 -and $parts[0] -eq '.store-id')) { return $null }
    $full = [IO.Path]::GetFullPath((Join-Path $SavesDir ($parts -join '\')))
    if (-not $full.StartsWith($SavesDir + '\', [StringComparison]::OrdinalIgnoreCase)) { return $null }
    return $full
}

function Remove-EmptyParents([string]$dir) {
    while ($dir -and $dir.StartsWith($SavesDir + '\', [StringComparison]::OrdinalIgnoreCase)) {
        if ((Test-Path $dir) -and -not (Get-ChildItem -Force -Path $dir | Select-Object -First 1)) {
            Remove-Item -Force -Path $dir
            $dir = Split-Path -Parent $dir
        } else { break }
    }
}

$TrashStamp = Get-Date -Format 'yyyy-MM-dd_HH-mm-ss'

function Invoke-Api($ctx) {
    $req = $ctx.Request
    $path = $req.Url.AbsolutePath
    $method = $req.HttpMethod

    if ($method -ne 'GET' -and $method -ne 'HEAD') {
        if (-not $req.Headers['X-MC-Save']) { Send-Text $ctx 403 'missing X-MC-Save header'; return }
        $origin = $req.Headers['Origin']
        if ($origin -and $origin -ne "http://localhost:$Port" -and $origin -ne "http://127.0.0.1:$Port") {
            Send-Text $ctx 403 'bad origin'; return
        }
        $clientStore = $req.Headers['X-MC-Store']
        if ($clientStore -and $clientStore -ne $StoreId) { Send-Text $ctx 409 'different saves folder'; return }
    }

    if ($path -eq '/api/ping') {
        Send-Json $ctx 200 @{ ok = $true; app = $AppTag; storeId = $StoreId }
        return
    }

    if ($path -eq '/api/saves' -and $method -eq 'GET') {
        $list = New-Object System.Collections.ArrayList
        foreach ($f in Get-SaveFiles) {
            $rel = $f.FullName.Substring($SavesDir.Length + 1).Replace('\', '/')
            [void]$list.Add(@{ p = $rel; m = (ConvertTo-UnixMs $f.LastWriteTimeUtc); s = $f.Length })
        }
        Send-Json $ctx 200 @{ storeId = $StoreId; files = $list.ToArray() }
        return
    }

    if ($path -eq '/api/saves/file') {
        $rel = $req.QueryString['p']
        $full = Resolve-SavePath $rel
        if (-not $full) { Send-Text $ctx 400 'bad path'; return }

        switch ($method) {
            { $_ -eq 'GET' -or $_ -eq 'HEAD' } {
                if (-not (Test-Path -LiteralPath $full -PathType Leaf)) { Send-Text $ctx 404 'not found'; return }
                $bytes = [IO.File]::ReadAllBytes($full)
                Send-Bytes $ctx 200 'application/octet-stream' $bytes
                return
            }
            'PUT' {
                $bytes = Read-Body $req
                $dir = Split-Path -Parent $full
                New-Item -ItemType Directory -Force -Path $dir | Out-Null
                $tmp = "$full.mcsave-tmp"
                [IO.File]::WriteAllBytes($tmp, $bytes)
                if (Test-Path -LiteralPath $full) {
                    try {
                        [IO.File]::Replace($tmp, $full, $null)
                    } catch {
                        [IO.File]::Delete($full)
                        [IO.File]::Move($tmp, $full)
                    }
                } else {
                    [IO.File]::Move($tmp, $full)
                }
                $m = 0L
                if ([long]::TryParse($req.QueryString['m'], [ref]$m) -and $m -gt 0) {
                    [IO.File]::SetLastWriteTimeUtc($full, (ConvertFrom-UnixMs $m))
                }
                $fi = New-Object IO.FileInfo($full)
                Send-Json $ctx 200 @{ ok = $true; m = (ConvertTo-UnixMs $fi.LastWriteTimeUtc); s = $fi.Length }
                return
            }
            'DELETE' {
                if (-not (Test-Path -LiteralPath $full -PathType Leaf)) { Send-Json $ctx 200 @{ ok = $true; missing = $true }; return }
                $relWin = $full.Substring($SavesDir.Length + 1)
                $dest = Join-Path (Join-Path $TrashDir $TrashStamp) $relWin
                New-Item -ItemType Directory -Force -Path (Split-Path -Parent $dest) | Out-Null
                if (Test-Path -LiteralPath $dest) { Remove-Item -LiteralPath $dest -Force }
                [IO.File]::Move($full, $dest)
                Remove-EmptyParents (Split-Path -Parent $full)
                Write-Info "  moved to trash: $relWin"
                Send-Json $ctx 200 @{ ok = $true }
                return
            }
        }
        Send-Text $ctx 405 'method not allowed'
        return
    }

    Send-Text $ctx 404 'unknown api'
}

function Invoke-Static($ctx) {
    $req = $ctx.Request
    if ($req.HttpMethod -ne 'GET' -and $req.HttpMethod -ne 'HEAD') { Send-Text $ctx 405 'method not allowed'; return }

    $rel = [Uri]::UnescapeDataString($req.Url.AbsolutePath).TrimStart('/')
    if ($rel -eq '') { $rel = 'index.html' }
    $full = [IO.Path]::GetFullPath((Join-Path $Root $rel.Replace('/', '\')))
    if (-not $full.StartsWith($Root + '\', [StringComparison]::OrdinalIgnoreCase)) { Send-Text $ctx 403 'forbidden'; return }
    $top = $full.Substring($Root.Length + 1).Split('\')[0]
    if ($top -eq 'saves' -or $top -eq 'backups' -or $top -eq 'launcher') { Send-Text $ctx 404 'not found'; return }
    if (-not (Test-Path -LiteralPath $full -PathType Leaf)) { Send-Text $ctx 404 'not found'; return }

    $ext = [IO.Path]::GetExtension($full).ToLowerInvariant()
    $type = $Mime[$ext]
    if (-not $type) { $type = 'application/octet-stream' }

    $res = $ctx.Response
    $res.StatusCode = 200
    $res.ContentType = $type
    $res.Headers['Cache-Control'] = 'no-cache'
    $fs = [IO.File]::OpenRead($full)
    try {
        $res.ContentLength64 = $fs.Length
        if ($req.HttpMethod -ne 'HEAD') { $fs.CopyTo($res.OutputStream) }
    } finally {
        $fs.Dispose()
        $res.OutputStream.Close()
    }
}

$AppProfileDir = Join-Path $env:LOCALAPPDATA 'MCPE-Web\app-window'

function Find-AppBrowser {
    $found = @()
    foreach ($exe in 'msedge.exe', 'chrome.exe') {
        foreach ($hive in 'HKCU:', 'HKLM:') {
            $key = "$hive\SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\$exe"
            $p = (Get-ItemProperty -Path $key -ErrorAction SilentlyContinue).'(default)'
            if ($p) { $found += $p.Trim('"') }
        }
        if ($exe -eq 'msedge.exe') {
            $found += "${env:ProgramFiles(x86)}\Microsoft\Edge\Application\msedge.exe"
            $found += "$env:ProgramFiles\Microsoft\Edge\Application\msedge.exe"
        } else {
            $found += "$env:ProgramFiles\Google\Chrome\Application\chrome.exe"
            $found += "$env:LOCALAPPDATA\Google\Chrome\Application\chrome.exe"
        }
    }
    foreach ($p in $found) { if ($p -and (Test-Path -LiteralPath $p)) { return $p } }
    return $null
}

function Open-AppWindow([string]$browser) {
    New-Item -ItemType Directory -Force -Path $AppProfileDir | Out-Null
    $argList = @(
        "--app=$Url",
        "--user-data-dir=`"$AppProfileDir`"",
        '--window-size=1280,760',
        '--no-first-run',
        '--no-default-browser-check',
        '--disable-features=Translate',
        '--autoplay-policy=no-user-gesture-required'
    )
    Start-Process -FilePath $browser -ArgumentList $argList | Out-Null
}

function Get-AppBrowserProcessId {
    $needle = $AppProfileDir.ToLowerInvariant()
    $procs = Get-CimInstance Win32_Process -Filter "Name = 'msedge.exe' OR Name = 'chrome.exe'" -ErrorAction SilentlyContinue
    foreach ($p in $procs) {
        $cmd = [string]$p.CommandLine
        if ($cmd -and $cmd.ToLowerInvariant().Contains($needle) -and $cmd -notmatch '--type=') {
            return [int]$p.ProcessId
        }
    }
    return $null
}

function Open-Game {
    if ($NoBrowser) { return 'none' }
    if (-not $Tab) {
        $browser = Find-AppBrowser
        if ($browser) { Open-AppWindow $browser; return 'app' }
    }
    Start-Process $Url
    return 'tab'
}

try {
    $ping = Invoke-RestMethod -Uri "${Url}api/ping" -TimeoutSec 2 -ErrorAction Stop
    if ($ping.app -eq $AppTag) {
        [void](Open-Game)
        exit 0
    }
} catch { }

$listener = New-Object Net.HttpListener
$listener.Prefixes.Add($Url)
try {
    $listener.Start()
} catch {
    Show-Error ("Couldn't start the game's local server on port $Port.`n`n" +
        "Something else is probably using that port. Close it, or change the port number in " +
        "'Launch Game.bat'.`n`n($($_.Exception.Message))")
    exit 1
}

$mode = Open-Game
if ($mode -ne 'app') { Show-Console }

New-SavesBackup

Write-Host ""
Write-Good  "Minecraft PE is running at $Url"
Write-Info  "Worlds are saved to: $SavesDir"
Write-Info  "Backups (one per launch, newest $MaxBackups kept): $BackupDir"
Write-Host ""
if ($mode -ne 'app') {
    Write-Warn2 "Keep this window open while you play. Close it when you're done."
    Write-Host ""
}

$appPid = $null
$appSeenAt = $null
$launchedAt = Get-Date
$nextAppCheck = Get-Date
$closedAt = $null

try {
    while ($listener.IsListening) {
        $async = $listener.BeginGetContext($null, $null)
        while (-not $async.AsyncWaitHandle.WaitOne(250)) {
            if ($mode -ne 'app') { continue }
            $now = Get-Date
            if ($closedAt) {
                if (($now - $closedAt).TotalSeconds -ge 4) { return }
                continue
            }
            if ($now -lt $nextAppCheck) { continue }
            $nextAppCheck = $now.AddSeconds(1)

            if ($appPid -and (Get-Process -Id $appPid -ErrorAction SilentlyContinue)) { continue }
            $appPid = Get-AppBrowserProcessId
            if ($appPid) { $appSeenAt = $now; continue }
            if ($appSeenAt) {
                $closedAt = $now
            } elseif (($now - $launchedAt).TotalSeconds -gt 30) {
                $mode = 'tab'
                Show-Console
                Write-Warn2 "Keep this window open while you play. Close it when you're done."
            }
        }
        $ctx = $listener.EndGetContext($async)
        try {
            $hostName = $ctx.Request.Url.Host
            if ($hostName -ne 'localhost' -and $hostName -ne '127.0.0.1') {
                Send-Text $ctx 403 'forbidden host'
            } elseif ($ctx.Request.Url.AbsolutePath.StartsWith('/api/')) {
                Invoke-Api $ctx
            } else {
                Invoke-Static $ctx
            }
        } catch {
            $msg = $_.Exception.Message
            if ($msg -notmatch 'network name is no longer available|connection was forcibly closed|The specified network name') {
                Write-Warn2 "Request failed: $($ctx.Request.HttpMethod) $($ctx.Request.Url.PathAndQuery) - $msg"
            }
            try { $ctx.Response.StatusCode = 500; $ctx.Response.Close() } catch { }
        }
    }
} finally {
    $listener.Stop()
    $listener.Close()
}
