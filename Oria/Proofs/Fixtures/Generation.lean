module

public import Oria.Proofs.Fixtures.Batch.ContentCommon
public import Oria.Datapack
public meta import Oria.Proofs.Fixtures.Batch.ContentCommon
public meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.Generation
open Oria.Std Oria.Std.Command.Arg Oria.Datapack
open Oria.Proofs.Fixtures.Batch (capture input bp bx setup)

@[mcfunction]
public def biomeCube := capture (FillBiome.run (bx 0 0 0 7 7 7) "minecraft:plains")

@[mcfunction]
public def biomeSingle := capture (FillBiome.run (bx 1 1 1 2 2 2) "minecraft:desert")

@[mcfunction]
public def biomeFiltered := capture (FillBiome.run (bx 0 0 0 7 7 7) "minecraft:forest" (some (.id "minecraft:plains")))

@[mcfunction]
public def biomeTag := capture (FillBiome.run (bx 0 0 0 7 7 7) "minecraft:desert" (some (.tag "minecraft:is_overworld")))

@[mcfunction]
public def biomeNoMatch := capture (FillBiome.run (bx 0 0 0 7 7 7) "minecraft:plains" (some (.id "minecraft:the_end")))

@[mcfunction]
public def biomeTooLarge := capture (FillBiome.run (bx 0 0 0 512 64 512) "minecraft:plains")

@[mcfunction]
public def featureNamed := capture (Place.feature (Feature.named "generation:gold"))

@[mcfunction]
public def featureInline := capture (Place.feature (Feature.ofNbt (nbt% {type: "minecraft:simple_block", to_place: {id: "minecraft:diamond_block"}})) (bp 1 0 0))

@[mcfunction]
public def featureFailure := capture (Place.feature (Feature.ofNbt (nbt% {type: "minecraft:simple_block", to_place: {id: "minecraft:dead_bush"}})))

@[mcfunction]
public def jigsaw := capture (Place.jigsaw "generation:pool" "generation:start" (.static 1) (bp 8 0 0))

@[mcfunction]
public def jigsawAbsent := capture (Place.jigsaw "generation:pool" "generation:absent" (.static 1) (bp 8 0 0))

@[mcfunction]
public def «structure» := capture (Place.structure "minecraft:igloo" (bp 80 0 0))

@[mcfunction]
public def template := capture (Place.template "generation:template")

@[mcfunction]
public def template90 := capture (Place.template "generation:template" .here {rotation := .clockwise90})

@[mcfunction]
public def template180 := capture (Place.template "generation:template" .here {rotation := .clockwise180})

@[mcfunction]
public def template270 := capture (Place.template "generation:template" .here {rotation := .counterclockwise90})

@[mcfunction]
public def templateMirrorX := capture (Place.template "generation:template" .here {mirror := .frontBack})

@[mcfunction]
public def templateMirrorZ := capture (Place.template "generation:template" .here {mirror := .leftRight})

@[mcfunction]
public def templateStrict := capture (Place.template "generation:template" .here {strict := true})

@[mcfunction]
public def templateSeeded := capture (Place.template "generation:template" .here {integrity := .decimal 0.5, seed := .static 123})

@[mcfunction]
public def templateZero := capture (Place.template "generation:template" .here {integrity := .static 0, seed := .static 123})

@[mcfunction]
public def templateMissing := capture (Place.template "generation:absent")

@[mcfunction]
public def waypointList := capture (Waypoint.list)

@[mcfunction]
public def waypointRed := capture (Waypoint.modify .self (.color (some .red)))

@[mcfunction]
public def waypointHex := capture (Waypoint.modify .self (.hex "6495ED"))

@[mcfunction]
public def waypointShortHex := capture (Waypoint.modify .self (.hex "f0A"))

@[mcfunction]
public def waypointColorReset := capture (Waypoint.modify .self (.color none))

@[mcfunction]
public def waypointStyle := capture (Waypoint.modify .self (.style (some "minecraft:bowtie")))

@[mcfunction]
public def waypointStyleReset := capture (Waypoint.modify .self (.style none))

@[mcfunction]
public def waypointMissing := capture (Waypoint.modify
  (.selector (.allEntities {tags := [.include "generation.absent"], limit := some 1})) (.color (some .red)))

@[mcfunction]
public def watchCreate := capture (Stopwatch.create "generation:lap")

@[mcfunction]
public def watchQuery := capture (Stopwatch.query "generation:lap")

@[mcfunction]
public def watchMillis := capture (Stopwatch.query "generation:lap" (.static 1000))

@[mcfunction]
public def watchFraction := capture (Stopwatch.query "generation:lap" (.decimal 0.5))

@[mcfunction]
public def watchNegative := capture (Stopwatch.query "generation:lap" (.static (-1000)))

@[mcfunction]
public def watchZero := capture (Stopwatch.query "generation:lap" (.static 0))

@[mcfunction]
public def watchRestart := capture (Stopwatch.restart "generation:lap")

@[mcfunction]
public def watchRemove := capture (Stopwatch.remove "generation:lap")

@[mcfunction]
public def biomeDynamic := input (g := FillBiome.grade (bx 0 0 0 7 7 7)) fun n => do
  FillBiome.run ⟨bp 0 0 0, .world (.relative (.dynamic n)) (.relative (.static 7)) (.relative (.static 7))⟩
    "minecraft:savanna"

@[mcfunction]
public def jigsawDynamic := input (g := Place.grade .here) fun n => do
  Place.jigsaw "generation:pool" "generation:start" (.dynamic n) (bp 8 0 0)

@[mcfunction]
public def templateDynamic := input (g := Place.grade .here) fun n => do
  Place.template "generation:template" .here {integrity := .dynamic n, seed := .dynamic n}

@[mcfunction]
public def featureDynamic := input (g := Place.grade .here) fun n => do
  Place.feature (Feature.named "generation:gold")
    (.world (.relative (.dynamic n)) (.relative (.static 0)) (.relative (.static 0)))

@[mcfunction]
public def watchDynamic := input (g := Stopwatch.grade) fun n => do
  Stopwatch.query "generation:lap" (.dynamic n)

@[datapack]
public def specimen : Spec := build {ns := "generation", registerBudget := 6} do
  onLoad setup.ref
  entry "biomecube" biomeCube.ref
  entry "biomesingle" biomeSingle.ref
  entry "biomefiltered" biomeFiltered.ref
  entry "biometag" biomeTag.ref
  entry "biomenomatch" biomeNoMatch.ref
  entry "biometoolarge" biomeTooLarge.ref
  entry "featurenamed" featureNamed.ref
  entry "featureinline" featureInline.ref
  entry "featurefailure" featureFailure.ref
  entry "jigsaw" jigsaw.ref
  entry "jigsawabsent" jigsawAbsent.ref
  entry "structure" «structure».ref
  entry "template" template.ref
  entry "template90" template90.ref
  entry "template180" template180.ref
  entry "template270" template270.ref
  entry "templatemirrorx" templateMirrorX.ref
  entry "templatemirrorz" templateMirrorZ.ref
  entry "templatestrict" templateStrict.ref
  entry "templateseeded" templateSeeded.ref
  entry "templatezero" templateZero.ref
  entry "templatemissing" templateMissing.ref
  entry "waypointlist" waypointList.ref
  entry "waypointred" waypointRed.ref
  entry "waypointhex" waypointHex.ref
  entry "waypointshorthex" waypointShortHex.ref
  entry "waypointcolorreset" waypointColorReset.ref
  entry "waypointstyle" waypointStyle.ref
  entry "waypointstylereset" waypointStyleReset.ref
  entry "waypointmissing" waypointMissing.ref
  entry "watchcreate" watchCreate.ref
  entry "watchquery" watchQuery.ref
  entry "watchmillis" watchMillis.ref
  entry "watchfraction" watchFraction.ref
  entry "watchnegative" watchNegative.ref
  entry "watchzero" watchZero.ref
  entry "watchrestart" watchRestart.ref
  entry "watchremove" watchRemove.ref
  entry "biomedynamic" biomeDynamic.ref
  entry "jigsawdynamic" jigsawDynamic.ref
  entry "templatedynamic" templateDynamic.ref
  entry "featuredynamic" featureDynamic.ref
  entry "watchdynamic" watchDynamic.ref

end Oria.Proofs.Fixtures.Generation
