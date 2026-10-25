scoreboard players reset #hook_skipped failure.results
scoreboard players set #hook_after failure.results 0
$function $(ns):__oria/load
execute unless score #hook_after failure.results matches 1 run scoreboard players set #ok oria.test 0
execute if score #hook_skipped failure.results matches 1 run scoreboard players set #ok oria.test 0
$execute unless data storage $(ns):persistent {roots:{"$(ns):seed":[3]}} run scoreboard players set #ok oria.test 0
scoreboard players set #input failure.results 4
scoreboard players set #zero failure.results 0
scoreboard players reset #missing failure.results
$execute store success score #success oria.test run function $(ns):run
execute unless score #success oria.test matches 1 run scoreboard players set #ok oria.test 0
execute unless score #before failure.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #skipped failure.results matches 0 run scoreboard players set #ok oria.test 0
execute unless score #continued failure.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #zero_result failure.results matches 0 run scoreboard players set #ok oria.test 0
execute unless score #default failure.results matches 42 run scoreboard players set #ok oria.test 0
execute unless score #captured failure.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #nested failure.results matches 44 run scoreboard players set #ok oria.test 0
execute unless score #fallback failure.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #outer failure.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #finished failure.results matches 1 run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime arena run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime stack run scoreboard players set #ok oria.test 0
scoreboard players set #input failure.results 12
$function $(ns):run
execute unless score #nested failure.results matches 86 run scoreboard players set #ok oria.test 0
$execute store success score #success oria.test run function $(ns):unhandled
execute unless score #success oria.test matches 0 run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime arena run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime stack run scoreboard players set #ok oria.test 0
execute unless score #skipped failure.results matches 0 run scoreboard players set #ok oria.test 0
