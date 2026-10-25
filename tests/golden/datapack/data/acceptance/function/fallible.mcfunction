execute if score #phase acceptance.oria matches 1.. run return fail
scoreboard players set #phase acceptance.oria 1
function acceptance:__oria/m10/b0
data modify storage acceptance:runtime "macro" set value {}
scoreboard players set #phase acceptance.oria 0
return 0
