execute if score #panic memory.oria matches 1 run return fail
execute store success score #p_ok memory.oria run execute store result score #p_result memory.oria run data get storage memory:persistent "slots"
execute unless score #p_ok memory.oria matches 1 run scoreboard players set #panic memory.oria 1
execute if score #p_result memory.oria matches 2147483647 run scoreboard players set #panic memory.oria 1
execute if score #panic memory.oria matches 1 run return fail
scoreboard players operation #p_result memory.oria += #p_one memory.oria
scoreboard players set #p_index memory.oria -1
scoreboard players operation #p_index memory.oria += #p_result memory.oria
execute store result storage memory:runtime "memory_arg"."p0" int 1 run scoreboard players get #p_index memory.oria
data modify storage memory:persistent "slots" append from storage memory:runtime "memory_draft"
execute store success score #p_ok memory.oria run execute store result score #p_used memory.oria run data get storage memory:persistent "used"
execute unless score #p_ok memory.oria matches 1 run scoreboard players set #panic memory.oria 1
execute store result storage memory:runtime "memory_next" int 1 run scoreboard players get #p_used memory.oria
function memory:__oria/persistent/next with storage memory:runtime "memory_arg"
function memory:__oria/persistent/stamp with storage memory:runtime "memory_arg"
execute store result storage memory:persistent "used" int 1 run scoreboard players get #p_result memory.oria
execute if score #panic memory.oria matches 1 run return fail
return 0
