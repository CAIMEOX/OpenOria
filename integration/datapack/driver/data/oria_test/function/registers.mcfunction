function register_test:run
execute unless score #sum register_test.oria matches 210 run scoreboard players set #ok oria.test 0
execute unless score #call register_test.oria matches 33 run scoreboard players set #ok oria.test 0
execute unless score #saved register_test.oria matches 51 run scoreboard players set #ok oria.test 0
execute if data storage register_test:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage register_test:runtime arena run scoreboard players set #ok oria.test 0
scoreboard players set #sum register_test.oria 0
scoreboard players set #call register_test.oria 0
scoreboard players set #saved register_test.oria 0
function register_zero:run
execute unless score #sum register_test.oria matches 210 run scoreboard players set #ok oria.test 0
execute unless score #call register_test.oria matches 33 run scoreboard players set #ok oria.test 0
execute unless score #saved register_test.oria matches 51 run scoreboard players set #ok oria.test 0
execute if data storage register_zero:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage register_zero:runtime arena run scoreboard players set #ok oria.test 0
scoreboard players set #registers_ran oria.test 1
