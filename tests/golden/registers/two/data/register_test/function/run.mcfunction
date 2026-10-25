execute if score #phase register_test.oria matches 1.. run return fail
scoreboard players set #phase register_test.oria 1
data modify storage register_test:runtime "stack" set value []
function register_test:__oria/m0/b0
data remove storage register_test:runtime "stack"
data modify storage register_test:runtime "macro" set value {}
scoreboard players set #phase register_test.oria 0
return 0
