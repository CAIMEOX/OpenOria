scoreboard objectives add oria.test dummy
scoreboard players set #ok oria.test 1
scoreboard players set #optimization_ran oria.test 0
function oria_test:optimization
execute unless score #optimization_ran oria.test matches 1 run scoreboard players set #ok oria.test 0
scoreboard players set #failure_ran oria.test 0
function oria_test:failure
execute unless score #failure_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

execute unless score #order acceptance.oria matches 12 run scoreboard players set #ok oria.test 0
execute unless score #loads acceptance.oria matches 1.. run scoreboard players set #ok oria.test 0
execute unless score #ticks acceptance.oria matches 1.. run scoreboard players set #ok oria.test 0
execute unless data storage acceptance:runtime macro run scoreboard players set #ok oria.test 0

kill @e[type=minecraft:marker,tag=oria_test_subject]
summon minecraft:marker ~ ~ ~ {Tags:["oria_test_subject"]}
execute store success score #success oria.test store result score #result oria.test as @e[type=minecraft:marker,tag=oria_test_subject,limit=1] at @s run function acceptance:home
execute unless score #success oria.test matches 1 run scoreboard players set #ok oria.test 0
execute unless score #result oria.test matches 0 run scoreboard players set #ok oria.test 0
execute positioned ~1 80 ~3 unless entity @e[type=minecraft:marker,tag=oria_test_subject,distance=..0.01] run scoreboard players set #ok oria.test 0

teleport @e[type=minecraft:marker,tag=oria_test_subject] ~ ~ ~
execute store success score #success oria.test store result score #result oria.test as @e[type=minecraft:marker,tag=oria_test_subject,limit=1] at @s run function acceptance:dynamic
execute unless score #success oria.test matches 1 run scoreboard players set #ok oria.test 0
execute unless score #result oria.test matches 0 run scoreboard players set #ok oria.test 0
execute positioned ~8 80 ~ unless entity @e[type=minecraft:marker,tag=oria_test_subject,distance=..0.01] run scoreboard players set #ok oria.test 0

scoreboard players set #input acceptance.oria 1
function acceptance:payload
execute unless score #payload acceptance.oria matches 42 run scoreboard players set #ok oria.test 0
execute if data storage acceptance:runtime arena run scoreboard players set #ok oria.test 0
execute if data storage acceptance:runtime draft run scoreboard players set #ok oria.test 0
scoreboard players reset #input acceptance.oria
function acceptance:payload
execute unless score #payload acceptance.oria matches 40 run scoreboard players set #ok oria.test 0
execute if data storage acceptance:runtime arena run scoreboard players set #ok oria.test 0

scoreboard players set #continued acceptance.oria 0
function acceptance:fallible
execute unless score #continued acceptance.oria matches 0 run scoreboard players set #ok oria.test 0
function acceptance:discarded
execute unless score #continued acceptance.oria matches 17 run scoreboard players set #ok oria.test 0
scoreboard players set #input acceptance.oria 9
function acceptance:fallible
execute unless score #continued acceptance.oria matches 9 run scoreboard players set #ok oria.test 0

scoreboard players operation #before oria.test = #loads acceptance.oria
scoreboard players add #before oria.test 1
function acceptance:__oria/load
execute unless score #order acceptance.oria matches 12 run scoreboard players set #ok oria.test 0
execute unless score #loads acceptance.oria = #before oria.test run scoreboard players set #ok oria.test 0
kill @e[type=minecraft:marker,tag=oria_test_subject]

scoreboard players set #memory_ran oria.test 0
function oria_test:persistent
execute unless score #memory_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #values_ran oria.test 0
function oria_test:values
execute unless score #values_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #registers_ran oria.test 0
function oria_test:registers
execute unless score #registers_ran oria.test matches 1 run scoreboard players set #ok oria.test 0
scoreboard players set #calls_ran oria.test 0
function oria_test:calls
execute unless score #calls_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #nbt_ran oria.test 0
function oria_test:nbt
execute unless score #nbt_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #standard_ran oria.test 0
function oria_test:standard
execute unless score #standard_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #data_compute_ran oria.test 0
function oria_test:data_compute
execute unless score #data_compute_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #execute_ran oria.test 0
function oria_test:execute
execute unless score #execute_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #flow_ran oria.test 0
function oria_test:flow
execute unless score #flow_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #runtime_nbt_ran oria.test 0
function oria_test:runtime_nbt
execute unless score #runtime_nbt_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

scoreboard players set #scoreboard_ran oria.test 0
function oria_test:scoreboard
execute unless score #scoreboard_ran oria.test matches 1 run scoreboard players set #ok oria.test 0

execute if score #ok oria.test matches 1 run setblock ~1 ~ ~ minecraft:redstone_block
execute unless score #ok oria.test matches 1 run setblock ~ ~ ~1 minecraft:redstone_block
