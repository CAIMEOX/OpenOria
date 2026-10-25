execute unless score #shared recursion_test.oria matches 169 run scoreboard players set #ok oria.test 0
execute unless score #record_before recursion_test.oria matches 235 run scoreboard players set #ok oria.test 0
execute unless score #record_after recursion_test.oria matches 356 run scoreboard players set #ok oria.test 0
execute unless score #local_fib recursion_test.oria matches 34 run scoreboard players set #ok oria.test 0
execute unless score #local_sum recursion_test.oria matches 218 run scoreboard players set #ok oria.test 0
execute unless score #host_recursion recursion_test.oria matches 7 run scoreboard players set #ok oria.test 0
execute unless score #native_index recursion_test.oria matches 21 run scoreboard players set #ok oria.test 0
execute unless score #host_index recursion_test.oria matches 13 run scoreboard players set #ok oria.test 0
execute unless score #native_equal_label recursion_test.oria matches 22 run scoreboard players set #ok oria.test 0
execute unless score #native_overflow recursion_test.oria matches -2147483648 run scoreboard players set #ok oria.test 0
execute unless score #native_negative recursion_test.oria matches 23 run scoreboard players set #ok oria.test 0
execute unless score #native_failure recursion_test.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless data storage recursion_test:result {buffer:{values:[[10,21]],label:"edited"}} run scoreboard players set #ok oria.test 0
execute unless data storage recursion_test:result {escaped:"literal $(p0): \"quoted\"\\\nnext"} run scoreboard players set #ok oria.test 0
scoreboard players reset #shared recursion_test.oria
scoreboard players reset #record_before recursion_test.oria
scoreboard players reset #record_after recursion_test.oria
scoreboard players reset #local_fib recursion_test.oria
scoreboard players reset #local_sum recursion_test.oria
scoreboard players reset #host_recursion recursion_test.oria
scoreboard players reset #native_index recursion_test.oria
scoreboard players reset #host_index recursion_test.oria
scoreboard players reset #native_equal_label recursion_test.oria
scoreboard players reset #native_overflow recursion_test.oria
scoreboard players reset #native_negative recursion_test.oria
scoreboard players reset #native_failure recursion_test.oria
data remove storage recursion_test:result buffer
data remove storage recursion_test:result escaped
