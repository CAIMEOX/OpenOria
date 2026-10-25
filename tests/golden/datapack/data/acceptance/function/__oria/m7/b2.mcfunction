data modify storage acceptance:runtime "draft" set value {"tag":0,"payload":[]}
data modify storage acceptance:runtime "arena" append from storage acceptance:runtime "draft"
scoreboard players add #heap_count acceptance.oria 1
scoreboard players set #r1 acceptance.oria 0
scoreboard players operation #r1 acceptance.oria -= #heap_count acceptance.oria
return run function acceptance:__oria/m7/b1
