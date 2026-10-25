execute if score #phase acceptance.oria matches 1.. run return fail
scoreboard players set #phase acceptance.oria 1
data modify storage acceptance:runtime "arena" set value []
scoreboard players set #heap_count acceptance.oria 0
function acceptance:__oria/m6/b0
data remove storage acceptance:runtime "arena"
data remove storage acceptance:runtime "draft"
data remove storage acceptance:runtime "heap_arg"
data remove storage acceptance:runtime "memory_arg"
data modify storage acceptance:runtime "macro" set value {}
scoreboard players set #phase acceptance.oria 0
return 0
