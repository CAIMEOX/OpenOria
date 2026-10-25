kill @e[type=minecraft:marker,tag=oria_execute]
kill @e[type=minecraft:marker,tag=oria_execute_observer]
summon minecraft:marker ~ ~ ~ {Tags:["oria_execute","oria_execute_a"]}
summon minecraft:marker ~ ~ ~ {Tags:["oria_execute","oria_execute_b"]}
summon minecraft:marker ~ ~ ~ {Tags:["oria_execute","oria_execute_c"]}
summon minecraft:marker ~ ~ ~ {Tags:["oria_execute_observer"]}
scoreboard players set #seed execute.oria 10
scoreboard players set #one execute.oria 1
scoreboard players set #count execute.oria 0
scoreboard players set @e[tag=oria_execute_a] execute.oria -10
scoreboard players set @e[tag=oria_execute_c] execute.oria 3
$execute as @e[tag=oria_execute_observer,limit=1] run function $(pack):fork
execute unless score @e[tag=oria_execute_a,limit=1] execute.oria matches 0 run scoreboard players set #ok oria.test 0
execute unless score @e[tag=oria_execute_c,limit=1] execute.oria matches 13 run scoreboard players set #ok oria.test 0
execute unless score @e[tag=oria_execute_a,limit=1] execute.result matches 0 run scoreboard players set #ok oria.test 0
execute unless score @e[tag=oria_execute_b,limit=1] execute.result matches 0 run scoreboard players set #ok oria.test 0
execute unless score @e[tag=oria_execute_c,limit=1] execute.result matches 13 run scoreboard players set #ok oria.test 0
execute unless score @e[tag=oria_execute_a,limit=1] execute.success matches 1 run scoreboard players set #ok oria.test 0
execute unless score @e[tag=oria_execute_b,limit=1] execute.success matches 0 run scoreboard players set #ok oria.test 0
execute unless score @e[tag=oria_execute_c,limit=1] execute.success matches 1 run scoreboard players set #ok oria.test 0
execute unless score #count execute.oria matches 2 run scoreboard players set #ok oria.test 0
execute unless score #after execute.oria matches 10 run scoreboard players set #ok oria.test 0
execute unless score #seed execute.oria matches 999 run scoreboard players set #ok oria.test 0
execute unless score @e[tag=oria_execute_observer,limit=1] execute.result matches 0 unless score @e[tag=oria_execute_observer,limit=1] execute.result matches 13 run scoreboard players set #ok oria.test 0
scoreboard players set #before execute.oria 0
scoreboard players set #cross execute.oria 0
scoreboard players set #outer execute.oria 0
$function $(pack):nested
execute unless score #before execute.oria matches 3 run scoreboard players set #ok oria.test 0
execute unless score #cross execute.oria matches 9 run scoreboard players set #ok oria.test 0
execute unless score #outer execute.oria matches 3 run scoreboard players set #ok oria.test 0
execute unless score #continued execute.oria matches 1 run scoreboard players set #ok oria.test 0
$execute as @e[tag=oria_execute_observer,limit=1] at @s run function $(pack):conditional
execute unless score @e[tag=oria_execute_observer,limit=1] execute.oria matches 77 run scoreboard players set #ok oria.test 0
execute unless entity @e[tag=oria_execute_a,distance=..0.01] run scoreboard players set #ok oria.test 0
execute positioned ~1 ~ ~ unless entity @e[tag=oria_execute_c,distance=..0.01] run scoreboard players set #ok oria.test 0
execute unless entity @e[tag=oria_execute_b,distance=..0.01] run scoreboard players set #ok oria.test 0
execute unless entity @e[tag=oria_execute_observer,distance=..0.01] run scoreboard players set #ok oria.test 0
scoreboard players set #skipped execute.oria 0
$function $(pack):empty
execute unless score #skipped execute.oria matches 0 run scoreboard players set #ok oria.test 0
execute unless score #continued execute.oria matches 2 run scoreboard players set #ok oria.test 0
$execute if data storage $(pack):runtime stack run scoreboard players set #ok oria.test 0
$execute if data storage $(pack):runtime arena run scoreboard players set #ok oria.test 0
kill @e[type=minecraft:marker,tag=oria_execute]
kill @e[type=minecraft:marker,tag=oria_execute_observer]
