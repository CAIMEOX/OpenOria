scoreboard objectives add native_test.vm dummy
scoreboard players set #index native_test.vm 2
function native_test:run
execute unless score #selected native_test.vm matches 3 run scoreboard players set #ok oria.test 0
execute unless score #ambiguous_continued native_test.vm matches 0 run scoreboard players set #ok oria.test 0
execute unless score #missing_continued native_test.vm matches 0 run scoreboard players set #ok oria.test 0
execute unless score #string_continued native_test.vm matches 0 run scoreboard players set #ok oria.test 0
execute unless data storage native_test:data {literal_a:"same",literal_b:"same"} run scoreboard players set #ok oria.test 0
execute if score #panic native_test.oria matches 1 run scoreboard players set #ok oria.test 0
execute unless data storage native_test:data {selected:[1,3],empty:[],computed:43} run scoreboard players set #ok oria.test 0
execute store result score #length oria.test run data get storage native_test:data selected
execute unless score #length oria.test matches 2 run scoreboard players set #ok oria.test 0
execute store result score #length oria.test run data get storage native_test:data empty
execute unless score #length oria.test matches 0 run scoreboard players set #ok oria.test 0
execute store result score #length oria.test run data get storage native_test:data nested
execute unless score #length oria.test matches 1 run scoreboard players set #ok oria.test 0
execute store result score #length oria.test run data get storage native_test:data nested[0]
execute unless score #length oria.test matches 3 run scoreboard players set #ok oria.test 0
execute unless data storage native_test:data copied{long:9223372036854775807L,tiny:0.0000000000000001d,text:'hello "world"',bytes:[B;-1b,2b],longs:[L;1L,3L]} run scoreboard players set #ok oria.test 0
execute unless data storage native_test:data macro_copy{long:9223372036854775807L,tiny:0.0000000000000001d,text:'hello "world"',bytes:[B;-1b,2b],longs:[L;1L,3L]} run scoreboard players set #ok oria.test 0
execute if data storage native_test:runtime arena run scoreboard players set #ok oria.test 0
execute if data storage native_test:runtime nbt_args run scoreboard players set #ok oria.test 0
execute if data storage native_test:runtime nbt_input run scoreboard players set #ok oria.test 0
execute if data storage native_test:runtime macro.p0 run scoreboard players set #ok oria.test 0
function native_test:gc
function native_test:restore
execute unless data storage native_test:data restored{long:9223372036854775807L,tiny:0.0000000000000001d,text:'hello "world"',bytes:[B;-1b,2b],longs:[L;1L,3L]} run scoreboard players set #ok oria.test 0
execute if score #panic native_test.oria matches 1 run scoreboard players set #ok oria.test 0

data remove storage native_test:data selected
data remove storage native_test:data empty
data remove storage native_test:data nested
data remove storage native_test:data computed
data remove storage native_test:data copied
data remove storage native_test:data macro_copy
data remove storage native_test:data restored
data remove storage native_test:data literal_a
data remove storage native_test:data literal_b
scoreboard players set #index native_test.vm 1
scoreboard players set #selected native_test.vm -1
function native_reg:run
execute unless score #selected native_test.vm matches 2 run scoreboard players set #ok oria.test 0
execute unless score #ambiguous_continued native_test.vm matches 0 run scoreboard players set #ok oria.test 0
execute unless score #missing_continued native_test.vm matches 0 run scoreboard players set #ok oria.test 0
execute unless score #string_continued native_test.vm matches 0 run scoreboard players set #ok oria.test 0
execute unless data storage native_test:data {computed:42,literal_a:"same",literal_b:"same",selected:[1,3]} run scoreboard players set #ok oria.test 0
execute unless data storage native_test:data copied{byte:-5b,short:-8s,integer:-2147483648,float:3.5f,ints:[I;1,-2]} run scoreboard players set #ok oria.test 0
execute if data storage native_reg:runtime arena run scoreboard players set #ok oria.test 0
execute if data storage native_reg:runtime nbt_args run scoreboard players set #ok oria.test 0
execute if data storage native_reg:runtime nbt_input run scoreboard players set #ok oria.test 0
execute if data storage native_reg:runtime macro.p0 run scoreboard players set #ok oria.test 0
function native_reg:gc
function native_reg:restore
execute unless data storage native_test:data restored{long:9223372036854775807L,tiny:0.0000000000000001d,byte:-5b,short:-8s,float:3.5f,ints:[I;1,-2]} run scoreboard players set #ok oria.test 0
execute if score #panic native_reg.oria matches 1 run scoreboard players set #ok oria.test 0
scoreboard players set #runtime_nbt_ran oria.test 1
