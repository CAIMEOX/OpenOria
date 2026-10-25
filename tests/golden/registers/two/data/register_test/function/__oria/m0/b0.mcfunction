data modify storage register_test:runtime "stack_draft" set value {"locals":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"saved":[],"result":[]}
data modify storage register_test:runtime "stack" append from storage register_test:runtime "stack_draft"
data remove storage register_test:runtime "stack_draft"
data modify storage register_test:runtime "stack"[-1]."locals"[17] set value 3
data modify storage register_test:runtime "stack"[-1]."locals"[16] set value 4
data modify storage register_test:runtime "stack"[-1]."locals"[15] set value 5
data modify storage register_test:runtime "stack"[-1]."locals"[14] set value 6
data modify storage register_test:runtime "stack"[-1]."locals"[13] set value 7
data modify storage register_test:runtime "stack"[-1]."locals"[12] set value 8
data modify storage register_test:runtime "stack"[-1]."locals"[11] set value 9
data modify storage register_test:runtime "stack"[-1]."locals"[10] set value 10
data modify storage register_test:runtime "stack"[-1]."locals"[9] set value 11
data modify storage register_test:runtime "stack"[-1]."locals"[8] set value 12
data modify storage register_test:runtime "stack"[-1]."locals"[7] set value 13
data modify storage register_test:runtime "stack"[-1]."locals"[6] set value 14
data modify storage register_test:runtime "stack"[-1]."locals"[5] set value 15
data modify storage register_test:runtime "stack"[-1]."locals"[4] set value 16
data modify storage register_test:runtime "stack"[-1]."locals"[3] set value 17
data modify storage register_test:runtime "stack"[-1]."locals"[2] set value 18
data modify storage register_test:runtime "stack"[-1]."locals"[1] set value 19
data modify storage register_test:runtime "stack"[-1]."locals"[0] set value 20
scoreboard players set #r1 register_test.oria 1
scoreboard players set #r0 register_test.oria 2
function register_test:__oria/m1/b0
scoreboard players operation #r0 register_test.oria = #ret0 register_test.oria
data remove storage register_test:runtime "stack"[-1]
execute store result storage register_test:runtime "macro"."p0" int 1 run scoreboard players get #r0 register_test.oria
function register_test:__oria/m0/b0/i1/macro with storage register_test:runtime "macro"
data modify storage register_test:runtime "stack_draft" set value {"locals":[0],"saved":[],"result":[]}
data modify storage register_test:runtime "stack" append from storage register_test:runtime "stack_draft"
data remove storage register_test:runtime "stack_draft"
scoreboard players set #r0 register_test.oria 4
function register_test:__oria/m2/b0
scoreboard players operation #r0 register_test.oria = #ret0 register_test.oria
data remove storage register_test:runtime "stack"[-1]
execute store result storage register_test:runtime "macro"."p0" int 1 run scoreboard players get #r0 register_test.oria
function register_test:__oria/m0/b0/i3/macro with storage register_test:runtime "macro"
scoreboard players set #r0 register_test.oria 4
function register_test:__oria/m4/b0
scoreboard players operation #r0 register_test.oria = #ret0 register_test.oria
execute store result storage register_test:runtime "macro"."p0" int 1 run scoreboard players get #r0 register_test.oria
function register_test:__oria/m0/b0/i5/macro with storage register_test:runtime "macro"
return 0
