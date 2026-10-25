execute unless score #loaded stdtest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #ticked stdtest.oria matches 1 run scoreboard players set #ok oria.test 0
scoreboard players set #min stdtest.oria 1
scoreboard players set #max stdtest.oria 6
scoreboard players set #seed stdtest.oria 42
scoreboard players set #out stdtest.oria -99
function stdtest:seed
function stdtest:sample
execute unless score #out stdtest.oria matches 1..6 run scoreboard players set #ok oria.test 0
scoreboard players operation #first oria.test = #out stdtest.oria
function stdtest:sample
function stdtest:seed
function stdtest:sample
execute unless score #out stdtest.oria = #first oria.test run scoreboard players set #ok oria.test 0

function stdtest:defaults
function stdtest:sample
scoreboard players operation #default oria.test = #out stdtest.oria
function stdtest:reset
function stdtest:sample
execute unless score #out stdtest.oria = #default oria.test run scoreboard players set #ok oria.test 0
function stdtest:clear
function stdtest:sample
execute unless score #out stdtest.oria = #default oria.test run scoreboard players set #ok oria.test 0

scoreboard players set #roll stdtest.oria -99
function stdtest:roll
execute unless score #roll stdtest.oria matches 1..6 run scoreboard players set #ok oria.test 0
scoreboard players set #continued stdtest.oria 0
function stdtest:stop
execute unless score #continued stdtest.oria matches 0 run scoreboard players set #ok oria.test 0
function stdtest:discard
execute unless score #continued stdtest.oria matches 2 run scoreboard players set #ok oria.test 0

scoreboard players set #min stdtest.oria 8
scoreboard players set #max stdtest.oria 8
scoreboard players set #out stdtest.oria -99
function stdtest:sample
execute unless score #out stdtest.oria matches -99 run scoreboard players set #ok oria.test 0
scoreboard players set #min stdtest.oria 9
scoreboard players set #max stdtest.oria 2
function stdtest:sample
execute unless score #out stdtest.oria matches -99 run scoreboard players set #ok oria.test 0
execute if data storage stdtest:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage stdtest:runtime arena run scoreboard players set #ok oria.test 0

scoreboard players set #chat stdtest.oria -99
function stdtest:chat
execute unless score #chat stdtest.oria matches -1 run scoreboard players set #ok oria.test 0
data modify storage stdtest:messages message set value {text:"Stored message"}
scoreboard players set #rich stdtest.oria 0
function stdtest:rich
execute unless score #rich stdtest.oria matches 1 run scoreboard players set #ok oria.test 0
scoreboard players set #out stdtest.oria 123
function stdtest:number
scoreboard players set #dialog stdtest.oria 99
function stdtest:dialog
execute unless score #dialog stdtest.oria matches -1 run scoreboard players set #ok oria.test 0
execute if data storage stdtest:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage stdtest:runtime arena run scoreboard players set #ok oria.test 0
data remove storage stdtest:messages message
scoreboard players set #standard_ran oria.test 1
