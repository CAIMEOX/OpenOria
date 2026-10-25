function dctest:storage
execute unless score #root dctest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #floor dctest.oria matches -4 run scoreboard players set #ok oria.test 0
execute unless score #scaled dctest.oria matches -7 run scoreboard players set #ok oria.test 0
execute unless score #length dctest.oria matches 6 run scoreboard players set #ok oria.test 0
execute unless score #count dctest.oria matches 5 run scoreboard players set #ok oria.test 0
execute unless data storage dctest:data root{copied:{x:1,y:2},slice:"bcde",suffix:"ef"} run scoreboard players set #ok oria.test 0
execute unless data storage dctest:data root{xs:[1,2,9,3,4],ys:[1,2,9,3,4]} run scoreboard players set #ok oria.test 0
execute store result score #slot oria.test run data get storage dctest:data root.xs[2]
execute unless score #slot oria.test matches 9 run scoreboard players set #ok oria.test 0
execute if data storage dctest:data root.drop run scoreboard players set #ok oria.test 0

scoreboard players set #input dctest.oria 1
function dctest:dynamic
execute unless score #dynamic dctest.oria matches 11 run scoreboard players set #ok oria.test 0
execute unless score #dynamic_root dctest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless data storage dctest:data root{mixed:{text:"$(literal)",n:1},xs:[1,7,2,9,3,4]} run scoreboard players set #ok oria.test 0
execute store result score #slot oria.test run data get storage dctest:data root.xs[1]
execute unless score #slot oria.test matches 7 run scoreboard players set #ok oria.test 0

function dctest:compute
execute unless score #sum dctest.oria matches 9 run scoreboard players set #ok oria.test 0
execute unless score #quotient dctest.oria matches -3 run scoreboard players set #ok oria.test 0
execute unless score #float dctest.oria matches -4 run scoreboard players set #ok oria.test 0
execute unless score #float_scaled dctest.oria matches -7 run scoreboard players set #ok oria.test 0
execute unless score #named dctest.oria matches 9 run scoreboard players set #ok oria.test 0
execute unless data storage dctest:data root{integer:12,float:3.5f} run scoreboard players set #ok oria.test 0
execute if data storage dctest:data root{integer:12L} run scoreboard players set #ok oria.test 0
execute if data storage dctest:data root{float:3.5d} run scoreboard players set #ok oria.test 0

scoreboard players set #stop dctest.oria 0
scoreboard players set #discard dctest.oria 0
scoreboard players set #unchanged dctest.oria 0
function dctest:failures
execute unless score #stop dctest.oria matches 0 run scoreboard players set #ok oria.test 0
execute unless score #discard dctest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #unchanged dctest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless data storage dctest:data root{integer:12,computed_default:0} run scoreboard players set #ok oria.test 0

summon minecraft:armor_stand ~ ~1 ~ {Tags:["dctest"],NoGravity:1b}
setblock ~4 ~1 ~ minecraft:chest
scoreboard players set @n[type=minecraft:armor_stand,tag=dctest] dctest.oria 37
function dctest:world
execute unless score #entity dctest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #context dctest.oria matches 37 run scoreboard players set #ok oria.test 0
execute unless score #block dctest.oria matches 6 run scoreboard players set #ok oria.test 0
execute unless data storage dctest:data root.entity.Invisible run scoreboard players set #ok oria.test 0
execute unless data storage dctest:data root{block:"Oria"} run scoreboard players set #ok oria.test 0
execute if data storage dctest:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage dctest:runtime arena run scoreboard players set #ok oria.test 0
kill @e[type=minecraft:armor_stand,tag=dctest]
setblock ~4 ~1 ~ minecraft:air
data remove storage dctest:data root
scoreboard players set #data_compute_ran oria.test 1
