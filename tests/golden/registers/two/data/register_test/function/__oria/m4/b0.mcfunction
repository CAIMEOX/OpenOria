scoreboard players operation #r1 register_test.oria = #r0 register_test.oria
scoreboard players add #r1 register_test.oria 5
scoreboard players add #r0 register_test.oria 1
data modify storage register_test:runtime "stack_draft" set value {"locals":[],"saved":[0],"result":[]}
data modify storage register_test:runtime "stack" append from storage register_test:runtime "stack_draft"
data remove storage register_test:runtime "stack_draft"
execute store result storage register_test:runtime "stack"[-1]."saved"[0] int 1 run scoreboard players get #r1 register_test.oria
function register_test:__oria/m5/b0
execute store result score #r1 register_test.oria run data get storage register_test:runtime "stack"[-1]."saved"[0]
scoreboard players operation #r0 register_test.oria = #ret0 register_test.oria
data remove storage register_test:runtime "stack"[-1]
scoreboard players operation #r1 register_test.oria += #r0 register_test.oria
scoreboard players operation #ret0 register_test.oria = #r1 register_test.oria
return 0
