data modify storage register_zero:runtime "stack_draft" set value {"locals":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"saved":[],"result":[]}
data modify storage register_zero:runtime "stack" append from storage register_zero:runtime "stack_draft"
data remove storage register_zero:runtime "stack_draft"
data modify storage register_zero:runtime "stack"[-1]."locals"[19] set value 1
data modify storage register_zero:runtime "stack"[-1]."locals"[18] set value 2
data modify storage register_zero:runtime "stack"[-1]."locals"[17] set value 3
data modify storage register_zero:runtime "stack"[-1]."locals"[16] set value 4
data modify storage register_zero:runtime "stack"[-1]."locals"[15] set value 5
data modify storage register_zero:runtime "stack"[-1]."locals"[14] set value 6
data modify storage register_zero:runtime "stack"[-1]."locals"[13] set value 7
data modify storage register_zero:runtime "stack"[-1]."locals"[12] set value 8
data modify storage register_zero:runtime "stack"[-1]."locals"[11] set value 9
data modify storage register_zero:runtime "stack"[-1]."locals"[10] set value 10
data modify storage register_zero:runtime "stack"[-1]."locals"[9] set value 11
data modify storage register_zero:runtime "stack"[-1]."locals"[8] set value 12
data modify storage register_zero:runtime "stack"[-1]."locals"[7] set value 13
data modify storage register_zero:runtime "stack"[-1]."locals"[6] set value 14
data modify storage register_zero:runtime "stack"[-1]."locals"[5] set value 15
data modify storage register_zero:runtime "stack"[-1]."locals"[4] set value 16
data modify storage register_zero:runtime "stack"[-1]."locals"[3] set value 17
data modify storage register_zero:runtime "stack"[-1]."locals"[2] set value 18
data modify storage register_zero:runtime "stack"[-1]."locals"[1] set value 19
data modify storage register_zero:runtime "stack"[-1]."locals"[0] set value 20
function register_zero:__oria/m1/b0
execute store result storage register_zero:runtime "stack"[-2]."locals"[0] int 1 run scoreboard players get #ret0 register_zero.oria
data remove storage register_zero:runtime "stack"[-1]
data modify storage register_zero:runtime "macro"."p0" set from storage register_zero:runtime "stack"[-1]."locals"[0]
function register_zero:__oria/m0/b0/i1/macro with storage register_zero:runtime "macro"
data modify storage register_zero:runtime "stack_draft" set value {"locals":[0,0,0],"saved":[],"result":[]}
data modify storage register_zero:runtime "stack" append from storage register_zero:runtime "stack_draft"
data remove storage register_zero:runtime "stack_draft"
data modify storage register_zero:runtime "stack"[-1]."locals"[0] set value 4
function register_zero:__oria/m2/b0
execute store result storage register_zero:runtime "stack"[-2]."locals"[0] int 1 run scoreboard players get #ret0 register_zero.oria
data remove storage register_zero:runtime "stack"[-1]
data modify storage register_zero:runtime "macro"."p0" set from storage register_zero:runtime "stack"[-1]."locals"[0]
function register_zero:__oria/m0/b0/i3/macro with storage register_zero:runtime "macro"
data modify storage register_zero:runtime "stack_draft" set value {"locals":[0,0],"saved":[],"result":[]}
data modify storage register_zero:runtime "stack" append from storage register_zero:runtime "stack_draft"
data remove storage register_zero:runtime "stack_draft"
data modify storage register_zero:runtime "stack"[-1]."locals"[0] set value 4
function register_zero:__oria/m4/b0
execute store result storage register_zero:runtime "stack"[-2]."locals"[0] int 1 run scoreboard players get #ret0 register_zero.oria
data remove storage register_zero:runtime "stack"[-1]
data modify storage register_zero:runtime "macro"."p0" set from storage register_zero:runtime "stack"[-1]."locals"[0]
function register_zero:__oria/m0/b0/i5/macro with storage register_zero:runtime "macro"
return 0
