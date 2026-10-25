scoreboard players operation #s0 acceptance.oria = #r0 acceptance.oria
scoreboard players operation #r0 acceptance.oria = #r1 acceptance.oria
scoreboard players operation #r1 acceptance.oria = #s0 acceptance.oria
scoreboard players set #heap_index acceptance.oria -1
scoreboard players operation #heap_index acceptance.oria -= #r0 acceptance.oria
execute store result storage acceptance:runtime "heap_arg"."p0" int 1 run scoreboard players get #heap_index acceptance.oria
function acceptance:__oria/m8/b2/i0/read with storage acceptance:runtime "heap_arg"
scoreboard players operation #r0 acceptance.oria += #r1 acceptance.oria
scoreboard players operation #ret0 acceptance.oria = #r0 acceptance.oria
return 0
