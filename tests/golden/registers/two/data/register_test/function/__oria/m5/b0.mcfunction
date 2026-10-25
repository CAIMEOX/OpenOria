scoreboard players operation #r1 register_test.oria = #r0 register_test.oria
scoreboard players add #r1 register_test.oria 1
scoreboard players add #r0 register_test.oria 2
scoreboard players operation #r1 register_test.oria *= #r0 register_test.oria
scoreboard players operation #ret0 register_test.oria = #r1 register_test.oria
return 0
