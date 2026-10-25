module

public import Oria.IR.DP121.Syntax
public import Oria.Nbt.Format

namespace Oria.Target.DP121

public def StoragePath.format (p : StoragePath) : Std.Format :=
  p.storage.text ++ " " ++ p.path.format

open Std Std.Format

private def score (s : Score) : Std.Format :=
  s.holder.token.text ++ " " ++ s.objective.token.text

private def formatScoreboard : Scoreboard → Std.Format
  | .objectiveAdd o => "scoreboard objectives add " ++ o.token.text ++ " dummy"
  | .set s v => "scoreboard players set " ++ score s ++ " " ++ toString v
  | .add s v _ => "scoreboard players add " ++ score s ++ " " ++ toString v
  | .remove s v _ => "scoreboard players remove " ++ score s ++ " " ++ toString v
  | .get s => "scoreboard players get " ++ score s
  | .operation l o r =>
      "scoreboard players operation " ++ score l ++ " " ++ o.token.text ++ " " ++ score r

private def dataPath {mode : Mode} : DataPath mode → Std.Format
  | .static p => p.format
  | .index p i suffix _ =>
      Nbt.formatSuffix (p.format ++ "[$(p" ++ toString i.val ++ ")]") suffix
  | .key p i suffix _ =>
      Nbt.formatSuffix (p.format ++ ".\"$(p" ++ toString i.val ++ ")\"") suffix

private def formatData {mode : Mode} : DataCommand mode → Std.Format
  | .setValue p v => "data modify storage " ++ dataPath p ++ " set value " ++ v.formatSnbt
  | .setFrom p q =>
      "data modify storage " ++ dataPath p ++ " set from storage " ++ dataPath q
  | .appendFrom p q =>
      "data modify storage " ++ dataPath p ++ " append from storage " ++ dataPath q
  | .remove p => "data remove storage " ++ dataPath p
  | .get p => "data get storage " ++ dataPath p

private def piece {mode : Mode} : Piece mode → Std.Format
  | .token t => t.text
  | .space => " "
  | .i32 v => toString v
  | .literal value => value.format
  | .parameter p => "$(p" ++ toString p.val ++ ")"

private def invocation {mode : Mode} {sig : Oria.Command.Signature}
    (i : Invocation mode sig) : Std.Format :=
  i.pieces.foldl (fun out p => out ++ piece p) ""

public def FragmentInvocation.format {mode : Mode} (i : FragmentInvocation mode) : Std.Format :=
  i.pieces.foldl (fun out p => out ++ piece p) ""

private def range (r : IntRange) : Std.Format :=
  match r.lower, r.upper with
  | some l, some u =>
      if l == u then toString l else toString l ++ ".." ++ toString u
  | some l, none => toString l ++ ".."
  | none, some u => ".." ++ toString u
  | none, none => ""

private def rel : ScoreRelation → Std.Format
  | .equal => "="
  | .less => "<"
  | .lessOrEqual => "<="
  | .greater => ">"
  | .greaterOrEqual => ">="

private def condition : ScoreCondition → Std.Format
  | .matches s r => "score " ++ score s ++ " matches " ++ range r
  | .compare l r x => "score " ++ score l ++ " " ++ rel r ++ " " ++ score x

private def storeTarget : StoreTarget → Std.Format
  | .score s => "score " ++ score s
  | .storageI32 p => "storage " ++ p.format ++ " int 1"

public def Command.format {mode : Mode} : Command mode → Std.Format
  | .scoreboard s => formatScoreboard s
  | .data d => formatData d
  | .invoke i => invocation i
  | .native i => i.format
  | .execute planned wrapper =>
      planned.format ++ " run function " ++ wrapper.id.render
  | .function f => "function " ++ f.id.render
  | .schedule f => "schedule function " ++ f.id.render ++ " 1t replace"
  | .commandLimit => "gamerule minecraft:max_command_sequence_length"
  | .functionWithStorage f s =>
      "function " ++ f.id.render ++ " with storage " ++ s.storage.text ++
        match s.path with
        | none => ""
        | some p => " " ++ p.format
  | .when p c x =>
      "execute " ++
        (match p with | .positive => "if " | .negative => "unless ") ++
        condition c ++ " run " ++ x.format
  | .store k t x =>
      "execute store " ++
        (match k with | .success => "success " | .result => "result ") ++
        storeTarget t ++ " run " ++ x.format
  | .returnValue v => "return " ++ toString v
  | .returnFail => "return fail"
  | .returnRun x => "return run " ++ x.format

public def FunctionBody.format {kind : FunctionKind} : FunctionBody kind → Std.Format
  | .plain xs => joinSep (xs.toList.map Command.format) line
  | .macro xs =>
      joinSep (xs.toList.map fun
        | .static c => c.format
        | .macro m => "$" ++ m.command.format) line

public def Command.pretty {mode : Mode} (c : Command mode) (width : Nat) : String :=
  c.format.pretty width

public def FunctionBody.pretty {kind : FunctionKind} (b : FunctionBody kind) (width : Nat) : String :=
  b.format.pretty width

end Oria.Target.DP121
