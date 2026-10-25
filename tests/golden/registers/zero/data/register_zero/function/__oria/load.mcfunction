execute if score #phase register_zero.oria matches 1.. run return fail
scoreboard objectives add register_zero.oria dummy
scoreboard players set #phase register_zero.oria 4
data modify storage register_zero:runtime "macro" set value {}
scoreboard players set #phase register_zero.oria 0
