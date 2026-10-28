# Minecraft: Rocket Edition

MCRE is Minecraft that runs in a browser tab. It started out as old Pocket Edition ported to the web, and
it's grown a lot since then. These days it plays a lot more like Java Edition, it runs Java mods, and you can
play with friends.

[**Play it here**](https://colinthepwner.github.io/MCRE/). Nothing to install, and it works on a computer
or a phone.

It's built on sangraphic's [MCPEweb](https://github.com/sangraphic/MCPEweb), which got Pocket Edition running
in the browser in the first place.

> **Disclaimer:** MCRE is an unofficial, non-commercial fan project. It isn't affiliated with, endorsed by, or
> connected to Mojang Studios or Microsoft. Minecraft is a trademark of Mojang Synergies AB, and the game, its
> art and its sounds belong to their owners. Nothing here is sold and no money is made from it. Mojang and
> Microsoft: if you'd like anything changed or taken down, open an issue and I'll deal with it right away. If
> you enjoy this, please go buy the real game!


## What's in it

- **Survival the way Java does it.** Hunger, sprinting, the Nether and the End, villages, weather, enchanting,
  anvils, brewing and redstone, plus the mobs and blocks from Java 1.5 up to 1.7. Mobs use Java's AI, so they
  actually find their way around things.
- **Lots of ways to make a world.** Any size up to infinite, Rocket terrain with the 1.7 biomes or the classic
  Pocket Edition terrain, Indev-style world types and themes, tall 256-block worlds, and your own seed. Skyblock
  and the 404 Challenge are there too.
- **Brutal difficulty**, one step past Hard. Monsters dig through dirt and wood to get at you, skeletons back
  off and keep shooting, creepers go off faster, and everything hits twice as hard. In return, creepers die in
  one hit and skeletons in two.
- **The old Xbox 360 tutorial.** Play Tutorial on the title screen loads the Title Update 3 tutorial world
  with its walkthrough, and I've added steps for sprinting and hunger.
- **Multiplayer.** Open your world to friends from the pause menu and they join with a short code. You don't
  need a server or any port forwarding. Chat, commands, operators and command blocks all work.
- **A helper bot.** Type `/bot spawn` and tell it what you need, like `/bot get 64 planks` or
  `/bot get iron set`. It gathers, crafts and smelts everything itself (mod items too) and brings it back.
  It can also follow you, guard you, clear an area or dig a tunnel, and if you hook up a chat AI in
  Options > Bot you can just talk to it normally.
- **It feels right on whatever you're using.** On a computer you get Java's title screen, menus, inventory and
  controls. On a phone or tablet you get touch controls built for it.

Signing in with a Microsoft account that owns Minecraft unlocks mods, multiplayer, Rocket terrain and the
bigger worlds. You can play without signing in, just with a smaller set of options.


## Mods

Mods load through **Rube**, the mod loader built into the game. It takes:

- **Rube mods.** New blocks, items, creatures, recipes, world generation, structures and scripts, made with
  JSON and JavaScript.
- **Java Edition mods.** Forge and ModLoader mods for 1.5.2 through 1.7.10, and Babric mods for Beta 1.7.3,
  running right in the browser.
- **ModPE scripts** from old Pocket Edition.
- **Resource packs.**
- **Structure files** (`.schematic`, `.schem` and `.nbt`).

There's a list of mods you can add with one click right in the Mods screen, and Minecraft Is Too Easy is
included as an optional game mode. If you want to make your own, the
[modding guide](https://colinthepwner.github.io/MCRE/modding.html) has everything, with examples.


## Playing on Windows

If you download the repo, double-click **`Launch Game.bat`**. The game opens in its own window (it uses
Microsoft Edge or Google Chrome for that), and closing the window shuts everything down. To play in a normal
browser tab instead, run `Launch Game.bat -Tab`.

When you play this way your worlds live in the `saves` folder next to the game, so clearing your browser data
won't touch them. Every launch makes a backup in `backups` (it keeps the newest 10), and worlds you delete in
the game go to `saves\.trash` instead of disappearing.


## Controls

| Action | Key |
| --- | --- |
| Move | W A S D |
| Look | Mouse (click the game to capture the cursor) |
| Break / attack | Left mouse button |
| Place / use | Right mouse button |
| Jump | Space |
| Sprint | Double-tap W, or hold Tab |
| Sneak | Shift |
| Fly (Creative) | Double-tap Space, then hold Space to go up and Shift to go down |
| Hotbar | 1-9 or the mouse wheel |
| Inventory | E |
| Drop item | Q (Ctrl+Q drops the whole stack) |
| Chat / command | T / `/` |
| Third person | F5 |
| Zoom | Z |
| Debug info | F3 |
| Fullscreen | F11 |
| Pause | Esc |

You can change most of these in Options > Controls.

In the inventory, the mouse works the way it does in Java: left and right click, drag to spread a stack,
double-click to gather, shift-click to move things over, and number keys to swap with the hotbar.

On a touchscreen, play in landscape. Drag on the lower left to walk (flick forward to sprint), drag anywhere
else to look, tap to place or use, and hold to break. Options > Controls has a D-pad if you'd rather use one.
In the inventory, tap an item and then tap where it should go.


## Building it yourself

The source is in `web-build.zip`. From the extracted `web-build` folder:

1. Install what it needs: `.\install_deps.ps1`
2. Build: `.\build.ps1`

That puts `index.html`, `index.js` and `index.wasm` in `project/emscripten`. Serve that folder and open it in
a browser.
