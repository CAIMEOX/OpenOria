execute store success score #reentry oria.test run function memory:increment
execute store success score #reentry_gc oria.test run function memory:gc
execute store success score #reentry_load oria.test run function memory:__oria/load
execute unless score #phase memory.oria matches 1 run scoreboard players set #ok oria.test 0
