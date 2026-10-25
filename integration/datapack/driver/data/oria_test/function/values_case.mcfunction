$function $(ns):arithmetic
execute unless score #quad value_test.oria matches 6543 run scoreboard players set #ok oria.test 0
execute unless score #recursive value_test.oria matches 1716 run scoreboard players set #ok oria.test 0
execute unless score #sparse value_test.oria matches 11 run scoreboard players set #ok oria.test 0
execute unless score #empty value_test.oria matches 1 run scoreboard players set #ok oria.test 0
$function $(ns):recovery
execute unless score #success value_test.oria matches 876 run scoreboard players set #ok oria.test 0
execute unless score #failure value_test.oria matches -1 run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime arena run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime stack run scoreboard players set #ok oria.test 0
$execute unless data storage $(ns):persistent roots."$(ns):triple"[2] run scoreboard players set #ok oria.test 0
$execute store result score #slots oria.test run data get storage $(ns):persistent slots
execute unless score #slots oria.test matches 3 run scoreboard players set #ok oria.test 0
$function $(ns):snapshot
execute unless score #root value_test.oria matches 543 run scoreboard players set #ok oria.test 0
execute unless score #ref value_test.oria matches 987 run scoreboard players set #ok oria.test 0
execute unless score #boxed value_test.oria matches 4321 run scoreboard players set #ok oria.test 0
execute unless score #link value_test.oria matches 19 run scoreboard players set #ok oria.test 0
$function $(ns):update
execute unless score #old value_test.oria matches 987 run scoreboard players set #ok oria.test 0
$function $(ns):gc
$function $(ns):__oria/load
$function $(ns):snapshot
execute unless score #root value_test.oria matches 1431 run scoreboard players set #ok oria.test 0
execute unless score #ref value_test.oria matches 1431 run scoreboard players set #ok oria.test 0
execute unless score #boxed value_test.oria matches 4321 run scoreboard players set #ok oria.test 0
execute unless score #link value_test.oria matches 19 run scoreboard players set #ok oria.test 0
$execute unless score #panic $(ns).oria matches 0 run scoreboard players set #ok oria.test 0
$execute if data storage $(ns):runtime stack run scoreboard players set #ok oria.test 0
