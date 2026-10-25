scoreboard players set #input opt.results 3
scoreboard players set #count opt.results 0
scoreboard players set #skipped opt.results 0
scoreboard players reset #missing opt.results
$execute store success score #success oria.test run function $(ns):run
execute unless score #success oria.test matches 1 run scoreboard players set #ok oria.test 0
execute unless score #count opt.results matches 9 run scoreboard players set #ok oria.test 0
execute unless score #next opt.results matches 4 run scoreboard players set #ok oria.test 0
execute unless score #neutral opt.results matches 3 run scoreboard players set #ok oria.test 0
execute unless score #neutral_min opt.results matches -2147483648 run scoreboard players set #ok oria.test 0
execute unless score #across opt.results matches 6 run scoreboard players set #ok oria.test 0
execute unless score #across_zero opt.results matches -3 run scoreboard players set #ok oria.test 0
execute unless score #threaded opt.results matches 4 run scoreboard players set #ok oria.test 0
execute unless score #threaded_negative opt.results matches -8 run scoreboard players set #ok oria.test 0
execute unless score #thread_path opt.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #selected_yes opt.results matches -6 run scoreboard players set #ok oria.test 0
execute unless score #selected_no opt.results matches 2 run scoreboard players set #ok oria.test 0
execute unless score #carried opt.results matches -3 run scoreboard players set #ok oria.test 0
execute unless score #joined opt.results matches 6 run scoreboard players set #ok oria.test 0
execute unless score #predicate opt.results matches 11 run scoreboard players set #ok oria.test 0
execute unless score #predicate_zero opt.results matches 13 run scoreboard players set #ok oria.test 0
execute unless score #varied opt.results matches 7 run scoreboard players set #ok oria.test 0
execute unless score #varied_negative opt.results matches -4 run scoreboard players set #ok oria.test 0
execute unless score #loop opt.results matches 6 run scoreboard players set #ok oria.test 0
execute unless score #constant_divisor opt.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #repeated opt.results matches 60 run scoreboard players set #ok oria.test 0
execute unless score #invalidation0 opt.results matches 66 run scoreboard players set #ok oria.test 0
execute unless score #invalidation1 opt.results matches 67 run scoreboard players set #ok oria.test 0
execute unless score #alias_missing opt.results matches 2 run scoreboard players set #ok oria.test 0
execute unless score #alias_present opt.results matches 20 run scoreboard players set #ok oria.test 0
execute unless score #join_path opt.results matches 2 run scoreboard players set #ok oria.test 0
execute if score #dead_join opt.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #projection opt.results matches 7 run scoreboard players set #ok oria.test 0
execute unless score #identity opt.results matches 3 run scoreboard players set #ok oria.test 0
execute unless score #bit opt.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #missing_bit opt.results matches 0 run scoreboard players set #ok oria.test 0
execute unless score #minimum_add opt.results matches -2147483645 run scoreboard players set #ok oria.test 0
execute unless score #minimum_sub opt.results matches -2147483645 run scoreboard players set #ok oria.test 0
execute unless score #minus_one opt.results matches 2 run scoreboard players set #ok oria.test 0
execute unless score #fork opt.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #negative opt.results matches -999 run scoreboard players set #ok oria.test 0
execute unless score #division opt.results matches -4 run scoreboard players set #ok oria.test 0
execute unless score #runtime_division opt.results matches -4 run scoreboard players set #ok oria.test 0
execute unless score #zero_failure opt.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #division_overflow opt.results matches -2147483648 run scoreboard players set #ok oria.test 0
execute unless score #overflow opt.results matches -2147483648 run scoreboard players set #ok oria.test 0
execute unless score #chosen opt.results matches 1 run scoreboard players set #ok oria.test 0
execute unless score #skipped opt.results matches 0 run scoreboard players set #ok oria.test 0
execute unless score #after opt.results matches 1 run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime arena run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime stack run scoreboard players set #ok oria.test 0
