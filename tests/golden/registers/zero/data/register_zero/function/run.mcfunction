execute if score #phase register_zero.oria matches 1.. run return fail
scoreboard players set #phase register_zero.oria 1
data modify storage register_zero:runtime "stack" set value []
data modify storage register_zero:runtime "stack_draft" set value {"locals":[0],"saved":[],"result":[]}
data modify storage register_zero:runtime "stack" append from storage register_zero:runtime "stack_draft"
data remove storage register_zero:runtime "stack_draft"
function register_zero:__oria/m0/b0
data remove storage register_zero:runtime "stack"[-1]
data remove storage register_zero:runtime "stack"
data modify storage register_zero:runtime "macro" set value {}
scoreboard players set #phase register_zero.oria 0
return 0
