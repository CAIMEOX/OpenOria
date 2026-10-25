execute if score #panic memory.oria matches 1 run return fail
scoreboard players set #p_one memory.oria 1
execute store success score #p_ok memory.oria run execute store result score #p_epoch memory.oria run data get storage memory:persistent "epoch"
execute unless score #p_ok memory.oria matches 1 run scoreboard players set #panic memory.oria 1
execute store success score #p_ok memory.oria run execute store result score #p_free memory.oria run data get storage memory:persistent "free"
execute unless score #p_ok memory.oria matches 1 run scoreboard players set #panic memory.oria 1
execute unless score #p_free memory.oria matches 1.. run return run function memory:__oria/persistent/allocate/append
execute if score #panic memory.oria matches 1 run return fail
scoreboard players operation #p_result memory.oria = #p_free memory.oria
scoreboard players set #p_index memory.oria -1
scoreboard players operation #p_index memory.oria += #p_result memory.oria
execute store result storage memory:runtime "memory_arg"."p0" int 1 run scoreboard players get #p_index memory.oria
function memory:__oria/persistent/read with storage memory:runtime "memory_arg"
execute store success score #p_ok memory.oria run execute store result score #p_next memory.oria run data get storage memory:runtime "memory_object"."next"
execute unless score #p_ok memory.oria matches 1 run scoreboard players set #panic memory.oria 1
function memory:__oria/persistent/replace with storage memory:runtime "memory_arg"
execute store success score #p_ok memory.oria run execute store result score #p_used memory.oria run data get storage memory:persistent "used"
execute unless score #p_ok memory.oria matches 1 run scoreboard players set #panic memory.oria 1
execute store result storage memory:runtime "memory_next" int 1 run scoreboard players get #p_used memory.oria
function memory:__oria/persistent/next with storage memory:runtime "memory_arg"
function memory:__oria/persistent/stamp with storage memory:runtime "memory_arg"
execute store result storage memory:persistent "free" int 1 run scoreboard players get #p_next memory.oria
execute store result storage memory:persistent "used" int 1 run scoreboard players get #p_result memory.oria
execute if score #panic memory.oria matches 1 run return fail
return 0
