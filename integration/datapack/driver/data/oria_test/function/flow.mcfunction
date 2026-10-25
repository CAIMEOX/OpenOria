function recursion_test:run
function recursion_test:elaboration
function oria_test:elaboration
execute unless score #sum recursion_test.oria matches 210 run scoreboard players set #ok oria.test 0
execute unless score #fib recursion_test.oria matches 34 run scoreboard players set #ok oria.test 0
execute unless score #captured recursion_test.oria matches 42 run scoreboard players set #ok oria.test 0
execute unless score #nested recursion_test.oria matches 20 run scoreboard players set #ok oria.test 0
execute unless score #accumulate recursion_test.oria matches 5050 run scoreboard players set #ok oria.test 0
execute unless score #comparisons recursion_test.oria matches 101 run scoreboard players set #ok oria.test 0
execute unless score #call_predicate recursion_test.oria matches 1012 run scoreboard players set #ok oria.test 0
execute unless score #ticks recursion_test.oria matches 1 run scoreboard players set #ok oria.test 0
execute if data storage recursion_test:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage recursion_test:runtime arena run scoreboard players set #ok oria.test 0
scoreboard players reset #sum recursion_test.oria
scoreboard players reset #fib recursion_test.oria
scoreboard players reset #captured recursion_test.oria
scoreboard players reset #nested recursion_test.oria
scoreboard players reset #accumulate recursion_test.oria
scoreboard players reset #comparisons recursion_test.oria
scoreboard players reset #call_predicate recursion_test.oria
scoreboard players reset #ticks recursion_test.oria
function recursion_zero:run
function recursion_zero:elaboration
function oria_test:elaboration
execute unless score #sum recursion_test.oria matches 210 run scoreboard players set #ok oria.test 0
execute unless score #fib recursion_test.oria matches 34 run scoreboard players set #ok oria.test 0
execute unless score #captured recursion_test.oria matches 42 run scoreboard players set #ok oria.test 0
execute unless score #nested recursion_test.oria matches 20 run scoreboard players set #ok oria.test 0
execute unless score #accumulate recursion_test.oria matches 5050 run scoreboard players set #ok oria.test 0
execute unless score #comparisons recursion_test.oria matches 101 run scoreboard players set #ok oria.test 0
execute unless score #call_predicate recursion_test.oria matches 1012 run scoreboard players set #ok oria.test 0
execute unless score #ticks recursion_test.oria matches 1 run scoreboard players set #ok oria.test 0
execute if data storage recursion_zero:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage recursion_zero:runtime arena run scoreboard players set #ok oria.test 0
scoreboard players set #i path_test.oria 1
scoreboard players set #j path_test.oria 0
scoreboard players set #exists path_test.oria 0
function path_test:run
execute unless score #read path_test.oria matches 20 run scoreboard players set #ok oria.test 0
execute unless score #last path_test.oria matches 21 run scoreboard players set #ok oria.test 0
execute unless score #constant path_test.oria matches 21 run scoreboard players set #ok oria.test 0
execute unless score #continued path_test.oria matches 0 run scoreboard players set #ok oria.test 0
execute unless score #exists path_test.oria matches 1 run scoreboard players set #ok oria.test 0
execute store result score #copy oria.test run data get storage path_test:data slots[0].x
execute unless score #copy oria.test matches 9 run scoreboard players set #ok oria.test 0
execute store result score #written oria.test run data get storage path_test:data slots[0]."two words"
execute unless score #written oria.test matches 42 run scoreboard players set #ok oria.test 0
execute if data storage path_test:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage path_test:runtime arena run scoreboard players set #ok oria.test 0
scoreboard players set #flow_ran oria.test 1
