# MCRE (Minecraft: Rocket Edition)

Minecraft Pocket Edition 0.6.1 alpha in the browser, with PC-style controls: mouse look, a
single-screen inventory with click-and-drag item handling, mouse wheel support and PC-strength mobs.
Touchscreens still get the original Pocket Edition controls.

[**PLAY NOW**](https://colinthepwner.github.io/MCRE/)

Based on [MCPEweb](https://github.com/sangraphic/MCPEweb).


## Play on Windows

Double-click **`Launch Game.bat`**. The game opens in its own window (Microsoft Edge or Google Chrome
is used behind the scenes); closing that window shuts everything down.

To play in a normal browser tab instead, run `Launch Game.bat -Tab`.

### Saves

Worlds are kept in the `saves` folder next to the game, so they survive clearing browser data. A
backup of that folder is made in `backups` every time the game starts (the newest 10 are kept).
Worlds removed in-game go to `saves\.trash` rather than being deleted.

### Controls (keyboard and mouse)

| Action | Key |
| --- | --- |
| Move | W A S D or arrow keys |
| Look | Mouse (click the game to capture the cursor) |
| Break / attack | Left mouse button |
| Place / use | Right mouse button |
| Jump | Space |
| Fly (Creative) | Double-tap Space; hold Space to rise, Shift to descend |
| Sneak | Shift |
| Hotbar | 1-9 or mouse wheel |
| Inventory and crafting | E |
| Drop item | Q (Ctrl+Q for the whole stack) |
| Pause and free the cursor | Esc (the pause menu has Options, including FOV) |

The cursor is only captured while playing; menus always use a normal cursor. Mouse sensitivity is in
the in-game Options.

### Touchscreen

Play in landscape. Drag anywhere on the lower left of the screen to walk; tap there to jump (hold a
second finger to keep jumping, or to fly up and down in creative). Drag elsewhere to look around,
tap to place or use, and hold to break. Options > Controls switches between this joystick, a D-pad
with a jump button, or an invisible joystick.

In the inventory: tap an item to select it, then tap where it should go. Hold to select half (or,
with something selected, to put one down), double-tap to move an item to the other section, and drag
an item to carry it. Tap a recipe to craft it, hold it to craft all.

### Inventory, chests and furnaces

| Action | Mouse / key |
| --- | --- |
| Pick up or put down a stack | Left click |
| Pick up half / put down one | Right click |
| Spread a stack evenly | Hold left click and drag over slots |
| Put one in each slot | Hold right click and drag over slots |
| Gather matching items | Double-click |
| Move to the other section | Shift-click (or shift and drag) |
| Move a single item | Mouse wheel over a slot |
| Swap with a hotbar slot | 1-9 over a slot |
| Drop | Q (Shift+Q for the whole stack), or click outside the window |
| Craft | Put items in the crafting grid (3x3 at a crafting table) and take the result; shift-click the result to craft as many as you can |
| Scroll lists | Mouse wheel |


### New worlds

When creating a world you can pick its size (up to Extreme, or Infinite, on a computer), an
Indev-style world type (Island, Inland, Floating or Flat) and theme (Hell, Paradise or Woods),
1.5-style biomes or the classic Pocket Edition terrain, and a seed.

### From Java 1.5

The Nether, villages, the 1.5 mobs, weather, hunger, maps, enchanting, anvils, experience, potions
and brewing, and the 1.5 redstone blocks, alongside a tabbed creative inventory.


## Build

The source is in `web-build.zip`. From the extracted `web-build` folder:

1. Install dependencies: `.\install_deps.ps1`
2. Build: `.\build.ps1`

Output: `project/emscripten/index.html`, `index.js`, `index.wasm`. Serve that folder to run.
