execute if score #phase register_test.oria matches 1.. run return fail
scoreboard objectives add register_test.oria dummy
scoreboard players set #phase register_test.oria 4
data modify storage register_test:runtime "macro" set value {}
scoreboard players set #phase register_test.oria 0
