execute unless score #ready memory.oria matches 1 run scoreboard players set #ok oria.test 0
function memory:snapshot
execute unless score #sum memory.oria matches -1 run scoreboard players set #ok oria.test 0
execute unless score #points memory.oria matches 0 run scoreboard players set #ok oria.test 0
function memory:reentry
execute unless score #reentry oria.test matches 0 run scoreboard players set #ok oria.test 0
execute unless score #reentry_gc oria.test matches 0 run scoreboard players set #ok oria.test 0
execute unless score #reentry_load oria.test matches 0 run scoreboard players set #ok oria.test 0
execute unless score #survived memory.oria matches 34 run scoreboard players set #ok oria.test 0
execute unless score #phase memory.oria matches 0 run scoreboard players set #ok oria.test 0

function memory:publish41
execute store result score #before oria.test run data get storage memory:persistent slots
function memory:retain
execute store result score #after oria.test run data get storage memory:persistent slots
scoreboard players add #before oria.test 1
execute unless score #after oria.test = #before oria.test run scoreboard players set #ok oria.test 0
function memory:cycle
function memory:increment
function memory:increment
function memory:gc
function memory:snapshot
execute unless score #sum memory.oria matches 82 run scoreboard players set #ok oria.test 0
execute unless score #saved memory.oria matches 82 run scoreboard players set #ok oria.test 0
execute unless score #ring memory.oria matches 73 run scoreboard players set #ok oria.test 0
execute unless score #points memory.oria matches 2 run scoreboard players set #ok oria.test 0
execute unless score #panic memory.oria matches 0 run scoreboard players set #ok oria.test 0
execute if data storage memory:runtime arena run scoreboard players set #ok oria.test 0

execute store result score #ptr oria.test run data get storage memory:persistent roots."memory:pair"[0]
scoreboard players remove #ptr oria.test 1
execute store result storage oria_test:args p int 1 run scoreboard players get #ptr oria.test
function oria_test:read-persistent with storage oria_test:args
execute store result score #left oria.test run data get storage oria_test:memory object.payload[0]
execute store result score #right oria.test run data get storage oria_test:memory object.payload[1]
execute unless score #left oria.test = #right oria.test run scoreboard players set #ok oria.test 0

function memory:publish42
function memory:replace-cycle
execute unless score #old memory.oria matches 73 run scoreboard players set #ok oria.test 0
function memory:gc
function memory:snapshot
execute unless score #sum memory.oria matches 84 run scoreboard players set #ok oria.test 0
execute unless score #saved memory.oria matches 82 run scoreboard players set #ok oria.test 0
execute unless score #ring memory.oria matches 88 run scoreboard players set #ok oria.test 0

function memory:release
function memory:gc
function memory:snapshot
execute unless score #saved memory.oria matches -1 run scoreboard players set #ok oria.test 0
execute store result score #free oria.test run data get storage memory:persistent free
execute unless score #free oria.test matches 1.. run scoreboard players set #ok oria.test 0
execute store result score #before oria.test run data get storage memory:persistent slots
function memory:publish41
execute store result score #after oria.test run data get storage memory:persistent slots
execute unless score #after oria.test = #before oria.test run scoreboard players set #ok oria.test 0
execute store result score #ptr oria.test run data get storage memory:persistent roots."memory:pair"[0]
execute unless score #ptr oria.test = #free oria.test run scoreboard players set #ok oria.test 0
function memory:gc
function memory:__oria/load
function memory:snapshot
execute unless score #sum memory.oria matches 82 run scoreboard players set #ok oria.test 0
execute unless score #points memory.oria matches 2 run scoreboard players set #ok oria.test 0
execute unless score #ring memory.oria matches 88 run scoreboard players set #ok oria.test 0
execute unless score #panic memory.oria matches 0 run scoreboard players set #ok oria.test 0

data modify storage oria_test:memory schema set from storage memory:persistent schema
data modify storage memory:persistent schema set value "different schema"
function memory:__oria/load
execute unless score #ready memory.oria matches 0 run scoreboard players set #ok oria.test 0
execute store result score #ptr oria.test run data get storage memory:persistent roots."memory:points"[0]
execute unless score #ptr oria.test matches 2 run scoreboard players set #ok oria.test 0
data modify storage memory:persistent schema set from storage oria_test:memory schema
function memory:__oria/load
execute unless score #ready memory.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #panic memory.oria matches 0 run scoreboard players set #ok oria.test 0
scoreboard players set #memory_ran oria.test 1
