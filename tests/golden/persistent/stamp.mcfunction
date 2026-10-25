$execute if score #p_epoch memory.oria matches 0 run data modify storage memory:persistent "slots"[$(p0)]."mark" set value 0
$execute if score #p_epoch memory.oria matches 1 run data modify storage memory:persistent "slots"[$(p0)]."mark" set value 1
