execute if score #phase acceptance.oria matches 1.. run return fail
scoreboard objectives add acceptance.oria dummy
scoreboard players set #phase acceptance.oria 4
data modify storage acceptance:runtime "macro" set value {}
scoreboard players set #phase acceptance.oria 0
function acceptance:__oria/hook/6
function acceptance:__oria/hook/7
function acceptance:__oria/hook/7
function acceptance:__oria/hook/9
