scoreboard players operation #s2 register_test.oria = #r0 register_test.oria
scoreboard players add #s2 register_test.oria 5
execute store result storage register_test:runtime "stack"[-1]."locals"[0] int 1 run scoreboard players get #s2 register_test.oria
scoreboard players operation #r1 register_test.oria = #r0 register_test.oria
scoreboard players add #r1 register_test.oria 1
scoreboard players operation #s0 register_test.oria = #r1 register_test.oria
scoreboard players operation #r1 register_test.oria = #r0 register_test.oria
scoreboard players operation #r0 register_test.oria = #s0 register_test.oria
function register_test:__oria/m3/b0
scoreboard players operation #r0 register_test.oria = #ret0 register_test.oria
execute store result score #s0 register_test.oria run data get storage register_test:runtime "stack"[-1]."locals"[0]
scoreboard players operation #r0 register_test.oria += #s0 register_test.oria
scoreboard players operation #ret0 register_test.oria = #r0 register_test.oria
return 0
