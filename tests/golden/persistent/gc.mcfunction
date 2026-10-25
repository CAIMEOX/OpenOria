execute if score #phase memory.oria matches 1.. run return fail
execute if score #task.phase memory.oria matches 1.. run return fail
execute unless score #ready memory.oria matches 1 run return fail
scoreboard players set #phase memory.oria 3
scoreboard players set #panic memory.oria 0
data modify storage memory:runtime "stack" set value []
data modify storage memory:runtime "stack_draft" set value {"locals":[0,0,0],"saved":[],"result":[]}
data modify storage memory:runtime "stack" append from storage memory:runtime "stack_draft"
data remove storage memory:runtime "stack_draft"
function memory:__oria/m17/b0
data remove storage memory:runtime "stack"[-1]
data remove storage memory:runtime "stack"
scoreboard players set #phase memory.oria 0
execute if score #panic memory.oria matches 1 run return fail
return 0
