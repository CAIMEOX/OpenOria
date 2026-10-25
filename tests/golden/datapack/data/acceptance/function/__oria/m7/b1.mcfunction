data modify storage acceptance:runtime "draft" set value {"tag":1,"payload":[0,0]}
execute store result storage acceptance:runtime "draft"."payload"[0] int 1 run scoreboard players get #r0 acceptance.oria
execute store result storage acceptance:runtime "draft"."payload"[1] int 1 run scoreboard players get #r1 acceptance.oria
data modify storage acceptance:runtime "arena" append from storage acceptance:runtime "draft"
scoreboard players add #heap_count acceptance.oria 1
scoreboard players set #r0 acceptance.oria 0
scoreboard players operation #r0 acceptance.oria -= #heap_count acceptance.oria
function acceptance:__oria/m9/b0
scoreboard players operation #r0 acceptance.oria = #ret0 acceptance.oria
scoreboard players operation #ret0 acceptance.oria = #r0 acceptance.oria
return 0
