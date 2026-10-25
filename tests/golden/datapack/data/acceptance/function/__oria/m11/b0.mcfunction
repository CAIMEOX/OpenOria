scoreboard players set #r1 acceptance.oria 0
scoreboard players set #r0 acceptance.oria 0
execute store success score #r1 acceptance.oria run execute store result score #r0 acceptance.oria run scoreboard players get #input acceptance.oria
execute unless score #r1 acceptance.oria matches 1 run return run function acceptance:__oria/m11/b2
execute store result storage acceptance:runtime "macro"."p0" int 1 run scoreboard players get #r0 acceptance.oria
function acceptance:__oria/m11/b1/i0/macro with storage acceptance:runtime "macro"
return 0
