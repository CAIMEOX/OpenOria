execute store result score #s2 register_zero.oria run data get storage register_zero:runtime "stack"[-1]."locals"[0]
scoreboard players add #s2 register_zero.oria 1
execute store result storage register_zero:runtime "stack"[-1]."locals"[1] int 1 run scoreboard players get #s2 register_zero.oria
execute store result score #s2 register_zero.oria run data get storage register_zero:runtime "stack"[-1]."locals"[0]
scoreboard players add #s2 register_zero.oria 2
execute store result storage register_zero:runtime "stack"[-1]."locals"[0] int 1 run scoreboard players get #s2 register_zero.oria
scoreboard players operation #s0 register_zero.oria = #s2 register_zero.oria
execute store result score #s2 register_zero.oria run data get storage register_zero:runtime "stack"[-1]."locals"[1]
scoreboard players operation #s2 register_zero.oria *= #s0 register_zero.oria
execute store result storage register_zero:runtime "stack"[-1]."locals"[0] int 1 run scoreboard players get #s2 register_zero.oria
scoreboard players operation #ret0 register_zero.oria = #s2 register_zero.oria
return 0
