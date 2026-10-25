scoreboard players set #p_result memory.oria 0
scoreboard players set #promote_plan memory.oria -1
$execute store success score #promote_found memory.oria run execute store result score #p_result memory.oria run data get storage memory:runtime "memo"."$(p0)"."dst"
$execute if score #promote_found memory.oria matches 1 run execute store result score #promote_plan memory.oria run data get storage memory:runtime "memo"."$(p0)"."plan"
execute if score #promote_found memory.oria matches 1 run execute unless score #promote_plan memory.oria matches 5 run scoreboard players set #panic memory.oria 1
execute if score #promote_found memory.oria matches 1 run execute unless score #promote_plan memory.oria matches 5 run return fail
execute if score #promote_found memory.oria matches 1 run return 0
$data modify storage memory:runtime "memory_object" set from storage memory:runtime "arena"[$(p0)]
execute store result score #promote_tag memory.oria run data get storage memory:runtime "memory_object"."tag"
execute if score #promote_tag memory.oria matches 1 run return run function memory:__oria/persistent/copy/5/0
scoreboard players set #panic memory.oria 1
return fail
