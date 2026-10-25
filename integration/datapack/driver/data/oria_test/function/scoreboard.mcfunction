# Setup is repeatable and preserves existing scores.
scoreboard players set #input sbtest.choice 41
scoreboard players set #input sbtest.other 9
function sbtest:setup
execute unless score #input sbtest.choice matches 41 run scoreboard players set #ok oria.test 0
execute unless score #input sbtest.other matches 9 run scoreboard players set #ok oria.test 0

# Catalog counts and duplicate-name failure are native command results.
execute store result score #objectives oria.test run scoreboard objectives list
scoreboard players add #objectives oria.test 1
function sbtest:add
execute unless score #status sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #result sbtest.oria = #objectives oria.test run scoreboard players set #ok oria.test 0
scoreboard players set #input sbtest.temporary 73
function sbtest:duplicate
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
execute unless score #input sbtest.temporary matches 73 run scoreboard players set #ok oria.test 0
function sbtest:enable-temporary
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
function sbtest:remove
scoreboard players remove #objectives oria.test 1
execute unless score #status sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #result sbtest.oria = #objectives oria.test run scoreboard players set #ok oria.test 0
function sbtest:remove
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
function sbtest:add
execute if score #input sbtest.temporary matches -2147483648..2147483647 run scoreboard players set #ok oria.test 0
function sbtest:remove

# Resetting one objective leaves other objectives intact; an absent score still succeeds.
function sbtest:reset
execute unless score #status sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #result sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
execute if score #input sbtest.choice matches -2147483648..2147483647 run scoreboard players set #ok oria.test 0
execute unless score #input sbtest.other matches 9 run scoreboard players set #ok oria.test 0
function sbtest:reset
execute unless score #status sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
function sbtest:reset-missing
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0

# Enabling creates a zero score; repeated enabling fails and set preserves the lock state.
function sbtest:enable
execute unless score #status sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #result sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless score #input sbtest.choice matches 0 run scoreboard players set #ok oria.test 0
function sbtest:enable
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
scoreboard players set #input sbtest.choice 5
function sbtest:enable
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
function sbtest:enable-wrong
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
function sbtest:reset-all
execute unless score #status sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
execute if score #input sbtest.choice matches -2147483648..2147483647 run scoreboard players set #ok oria.test 0
execute if score #input sbtest.other matches -2147483648..2147483647 run scoreboard players set #ok oria.test 0
function sbtest:reset-all
execute unless score #status sbtest.oria matches 1 run scoreboard players set #ok oria.test 0
function sbtest:enable
execute unless score #status sbtest.oria matches 1 run scoreboard players set #ok oria.test 0

# An executor can satisfy the coeffect while failing the runtime player check.
summon minecraft:marker ~ ~ ~ {Tags:["oria_scoreboard_subject"]}
scoreboard players set #n sbtest.oria -3
execute as @e[type=minecraft:marker,tag=oria_scoreboard_subject,limit=1] run function sbtest:trigger
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
execute as @e[type=minecraft:marker,tag=oria_scoreboard_subject,limit=1] run function sbtest:trigger-add
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
scoreboard players set #n sbtest.oria 0
execute as @e[type=minecraft:marker,tag=oria_scoreboard_subject,limit=1] run function sbtest:trigger-set
execute unless score #status sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
scoreboard players set #continued sbtest.oria 0
execute as @e[type=minecraft:marker,tag=oria_scoreboard_subject,limit=1] run function sbtest:stop
execute unless score #continued sbtest.oria matches 0 run scoreboard players set #ok oria.test 0
execute as @e[type=minecraft:marker,tag=oria_scoreboard_subject,limit=1] run function sbtest:discard
execute unless score #continued sbtest.oria matches 2 run scoreboard players set #ok oria.test 0
kill @e[type=minecraft:marker,tag=oria_scoreboard_subject]
execute if data storage sbtest:runtime stack run scoreboard players set #ok oria.test 0
execute if data storage sbtest:runtime arena run scoreboard players set #ok oria.test 0
scoreboard players set #scoreboard_ran oria.test 1
