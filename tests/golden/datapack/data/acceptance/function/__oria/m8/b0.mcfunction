scoreboard players set #heap_index acceptance.oria -1
scoreboard players operation #heap_index acceptance.oria -= #r0 acceptance.oria
execute store result storage acceptance:runtime "heap_arg"."p0" int 1 run scoreboard players get #heap_index acceptance.oria
function acceptance:__oria/m8/b0/i0/read with storage acceptance:runtime "heap_arg"
execute if score #r1 acceptance.oria matches 1 run return run function acceptance:__oria/m8/b1
execute if score #r1 acceptance.oria matches 2 run return run function acceptance:__oria/m8/b2
return fail
