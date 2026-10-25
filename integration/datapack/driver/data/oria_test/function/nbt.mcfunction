scoreboard players set #nbt_loaded oria.test 0
execute store success score #nbt_loaded oria.test run function oria_test:nbt-value
execute unless score #nbt_loaded oria.test matches 1 run scoreboard players set #ok oria.test 0
execute unless data storage oria_nbt:test {value:{small:-128b,medium:32767s,integer:-2147483648,large:9223372036854775807L,float32:1e-8f,float64:1.2345678901234567d,zero:-0.0d,tiny:5e-324d,huge:1.7976931348623157e308d}} run scoreboard players set #ok oria.test 0
execute unless data storage oria_nbt:test {value:{text:"line\n\"quoted\"\\$(literal)",bytes:[B;-128b,127b],ints:[I;-2147483648,2147483647],longs:[L;1L,-3L],mixed:[1,"two",{ready:1b}]}} run scoreboard players set #ok oria.test 0
execute unless data storage oria_nbt:test {"price$":7} run scoreboard players set #ok oria.test 0
execute unless data storage oria_nbt:test {value:{note:{text:"typed",counters:[1,2,3]}}} run scoreboard players set #ok oria.test 0
data remove storage oria_nbt:test value
data remove storage oria_nbt:test "price$"
scoreboard players set #nbt_ran oria.test 1
