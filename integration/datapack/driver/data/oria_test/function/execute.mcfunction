scoreboard objectives add execute.oria dummy
scoreboard objectives add execute.result dummy
scoreboard objectives add execute.success dummy
function oria_test:execute_case {pack:"execute"}
function oria_test:execute_case {pack:"execute_stack"}
scoreboard players set #execute_ran oria.test 1
