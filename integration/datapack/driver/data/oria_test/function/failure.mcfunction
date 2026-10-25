scoreboard objectives add failure.results dummy
function oria_test:failure_case {ns:"failure_test"}
function oria_test:failure_case {ns:"failure_zero"}
execute store success score #success oria.test run function failure_unready:run
execute unless score #success oria.test matches 0 run scoreboard players set #ok oria.test 0
execute unless score #ready failure_unready.oria matches 0 run scoreboard players set #ok oria.test 0
execute if data storage failure_unready:persistent roots."failure_unready:seed" run scoreboard players set #ok oria.test 0
execute if data storage failure_unready:runtime arena run scoreboard players set #ok oria.test 0
execute if data storage failure_unready:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage failure_unready:runtime initial_result run scoreboard players set #ok oria.test 0
scoreboard players set #failure_ran oria.test 1
