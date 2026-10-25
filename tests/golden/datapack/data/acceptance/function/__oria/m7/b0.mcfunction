data modify storage acceptance:runtime "draft" set value {"tag":1,"payload":[]}
data modify storage acceptance:runtime "arena" append from storage acceptance:runtime "draft"
scoreboard players add #heap_count acceptance.oria 1
scoreboard players set #r0 acceptance.oria 0
scoreboard players operation #r0 acceptance.oria -= #heap_count acceptance.oria
data modify storage acceptance:runtime "draft" set value {"tag":2,"payload":[0,0]}
data modify storage acceptance:runtime "draft"."payload"[0] set value 41
execute store result storage acceptance:runtime "draft"."payload"[1] int 1 run scoreboard players get #r0 acceptance.oria
data modify storage acceptance:runtime "arena" append from storage acceptance:runtime "draft"
scoreboard players add #heap_count acceptance.oria 1
scoreboard players set #r0 acceptance.oria 0
scoreboard players operation #r0 acceptance.oria -= #heap_count acceptance.oria
function acceptance:__oria/m8/b0
scoreboard players operation #r0 acceptance.oria = #ret0 acceptance.oria
scoreboard players set #r2 acceptance.oria 0
scoreboard players set #r1 acceptance.oria 0
execute store success score #r2 acceptance.oria run execute store result score #r1 acceptance.oria run scoreboard players get #input acceptance.oria
execute unless score #r2 acceptance.oria matches 1 run return run function acceptance:__oria/m7/b2
data modify storage acceptance:runtime "draft" set value {"tag":1,"payload":[0]}
execute store result storage acceptance:runtime "draft"."payload"[0] int 1 run scoreboard players get #r1 acceptance.oria
data modify storage acceptance:runtime "arena" append from storage acceptance:runtime "draft"
scoreboard players add #heap_count acceptance.oria 1
scoreboard players set #r1 acceptance.oria 0
scoreboard players operation #r1 acceptance.oria -= #heap_count acceptance.oria
return run function acceptance:__oria/m7/b1
