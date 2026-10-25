execute store result score #s2 register_zero.oria run data get storage register_zero:runtime "stack"[-1]."locals"[0]
scoreboard players add #s2 register_zero.oria 5
execute store result storage register_zero:runtime "stack"[-1]."locals"[1] int 1 run scoreboard players get #s2 register_zero.oria
execute store result score #s2 register_zero.oria run data get storage register_zero:runtime "stack"[-1]."locals"[0]
scoreboard players add #s2 register_zero.oria 1
execute store result storage register_zero:runtime "stack"[-1]."locals"[0] int 1 run scoreboard players get #s2 register_zero.oria
data modify storage register_zero:runtime "stack_draft" set value {"locals":[0,0],"saved":[],"result":[]}
data modify storage register_zero:runtime "stack" append from storage register_zero:runtime "stack_draft"
data remove storage register_zero:runtime "stack_draft"
data modify storage register_zero:runtime "stack"[-1]."locals"[0] set from storage register_zero:runtime "stack"[-2]."locals"[0]
function register_zero:__oria/m5/b0
execute store result storage register_zero:runtime "stack"[-2]."locals"[0] int 1 run scoreboard players get #ret0 register_zero.oria
data remove storage register_zero:runtime "stack"[-1]
execute store result score #s0 register_zero.oria run data get storage register_zero:runtime "stack"[-1]."locals"[0]
execute store result score #s2 register_zero.oria run data get storage register_zero:runtime "stack"[-1]."locals"[1]
scoreboard players operation #s2 register_zero.oria += #s0 register_zero.oria
execute store result storage register_zero:runtime "stack"[-1]."locals"[0] int 1 run scoreboard players get #s2 register_zero.oria
scoreboard players operation #ret0 register_zero.oria = #s2 register_zero.oria
return 0
