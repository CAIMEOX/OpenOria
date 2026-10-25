data modify storage memory:runtime "promote_frame" set value {"src":0,"dst":0}
execute store result storage memory:runtime "promote_frame"."src" int 1 run scoreboard players get #p_source memory.oria
data modify storage memory:runtime "promote_frame"."object" set from storage memory:runtime "memory_object"
data modify storage memory:runtime "promotion" append from storage memory:runtime "promote_frame"
data modify storage memory:runtime "memory_draft" set value {"d":7,"tag":1,"payload":[0,0]}
function memory:__oria/persistent/allocate
execute store result storage memory:runtime "promotion"[-1]."dst" int 1 run scoreboard players get #p_result memory.oria
scoreboard players set #p_index memory.oria -1
scoreboard players operation #p_index memory.oria += #p_result memory.oria
execute store result storage memory:runtime "memory_arg"."p0" int 1 run scoreboard players get #p_index memory.oria
function memory:__oria/persistent/read with storage memory:runtime "memory_arg"
data modify storage memory:runtime "promotion"[-1]."target" set from storage memory:runtime "memory_object"
data modify storage memory:runtime "promotion"[-1]."target"."payload" set from storage memory:runtime "promotion"[-1]."object"."payload"
execute store result score #p_result memory.oria run data get storage memory:runtime "promotion"[-1]."dst"
data modify storage memory:runtime "memo_entry" set value {"dst":0,"plan":5}
execute store result storage memory:runtime "memo_entry"."dst" int 1 run scoreboard players get #p_result memory.oria
execute store result score #p_source memory.oria run data get storage memory:runtime "promotion"[-1]."src"
scoreboard players set #promote_index memory.oria -1
scoreboard players operation #promote_index memory.oria -= #p_source memory.oria
execute store result storage memory:runtime "memory_arg"."p0" int 1 run scoreboard players get #promote_index memory.oria
function memory:__oria/persistent/copy/1/memo with storage memory:runtime "memory_arg"
execute store result score #p_source memory.oria run data get storage memory:runtime "promotion"[-1]."object"."payload"[0]
function memory:__oria/persistent/copy/6
execute store result storage memory:runtime "promotion"[-1]."target"."payload"[0] int 1 run scoreboard players get #p_result memory.oria
execute store result score #p_source memory.oria run data get storage memory:runtime "promotion"[-1]."object"."payload"[1]
function memory:__oria/persistent/copy/6
execute store result storage memory:runtime "promotion"[-1]."target"."payload"[1] int 1 run scoreboard players get #p_result memory.oria
execute store result score #p_result memory.oria run data get storage memory:runtime "promotion"[-1]."dst"
data modify storage memory:runtime "memory_draft" set from storage memory:runtime "promotion"[-1]."target"
scoreboard players set #p_index memory.oria -1
scoreboard players operation #p_index memory.oria += #p_result memory.oria
execute store result storage memory:runtime "memory_arg"."p0" int 1 run scoreboard players get #p_index memory.oria
function memory:__oria/persistent/replace with storage memory:runtime "memory_arg"
execute store result score #p_result memory.oria run data get storage memory:runtime "promotion"[-1]."dst"
data remove storage memory:runtime "promotion"[-1]
return 0
