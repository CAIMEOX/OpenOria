function calls_test:run
function oria_test:calls_results
execute if data storage calls_test:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage calls_test:runtime arena run scoreboard players set #ok oria.test 0
function calls_low:run
function oria_test:calls_results
execute if data storage calls_low:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage calls_low:runtime arena run scoreboard players set #ok oria.test 0
function calls_zero:run
function oria_test:calls_results
execute if data storage calls_zero:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage calls_zero:runtime arena run scoreboard players set #ok oria.test 0
scoreboard players set #calls_ran oria.test 1
