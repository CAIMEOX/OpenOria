# Oria engineering rules

## Library-first implementation

- Before implementing infrastructure, inspect Lean's standard library, official framework
  facilities, and established dependencies for an existing solution.
- Prefer a mature, maintained library over a handwritten helper. Reuse its data model and
  extension points instead of wrapping it with a competing mini-framework.
- Add a custom implementation only after recording the concrete requirement that available
  libraries do not meet. Keep it behind one deep module with a small interface.
- Do not introduce string-concatenation pretty printers, ad-hoc parsers, bespoke path utilities,
  repeated handwritten IR traversals, or custom collections when Lean already provides a robust
  abstraction.

## Oria-specific constraints

- Construct custom IR documents with `Std.Format`; render to `String` only at the final seam with
  an explicit width. Use `Lean.PrettyPrinter` directly for Lean `Syntax` or `Expr` adapters.
- Prefer dependent indices and theorem certificates over runtime tests. Add tests only for
  behavior those proofs cannot express, such as layout, module visibility, and diagnostics.
- Keep `Val` and `Prog` abstract. Treat `import all Oria...` as a trusted escape outside the safe
  language model.
- Treat `@[mcfunction]` as the only user-facing definition-reification seam. Do not restore a
  public `Builder.close`, recipe eliminator, or registry mutation API; any evaluator linkage must
  remain an inert, sealed compiler ABI.
- Use checked string literals where a registered domain type is expected. Register new literal
  interfaces with `[string_literal Constructor.ofString] Type` in the type's own module, reusing
  its validation rules and automatic proof arguments. Computed String inputs use `parse` or an
  explicit constructor with an existing proof. Keep semantic selector constructors explicit.
- Keep compilation stages explicit: Tree, Cont, Machine, and DP121. Target lowering consumes
  Machine representation and allocation metadata; Artifact handles file output.

## Validation

- Prefer source-to-datapack E2E fixtures for executable regressions. Construct programs with the
  public DSL, compile through the complete pipeline, and check the final datapack artifacts.
- For runtime behavior, exercise the generated datapack on the pinned Minecraft server and check
  observable results, effects, command failure, and invocation-storage lifetime.
- Use focused module checks for diagnostics, visibility, or module-specific contracts when they
  address a concrete validation need. Interface invariants retain the type/theorem-first rule.

## Standard library documentation

- Write public documentation, docstrings, examples, and documentation navigation in English.
- Keep Std interface contracts in declaration docstrings: parameters, native success/result,
  required context, effects, and staging behavior. Put module guides in Markdown module docs.
- Use Verso declaration docstrings and Lean-checked examples. Keep cross-command examples in
  `Oria.Examples.StandardLibrary`, which is checked by `OriaTests`.
- Use `doc-gen4` from `docbuild/` for the reference site and Lean's `linter.missingDocs` for
  coverage. Run `scripts/check-docs` after changing Std interfaces or documentation, and
  `scripts/docs` to rebuild the HTML site.

## Fast evolution

- Do not hesitate to refactor, rename, or delete code. Lean's type system and proof engine will
  catch regressions. Keep the codebase small and clean.
- We are still in a rapidly evolving design phase. Breaking changes are expected, when told to remove certain features, just delete them. Do not try to maintain backward compatibility with old code or old IR.
- 我们推崇 Functional Programming 的可推理风格：禁止可变对象、继承层次、
  service-style façade 和没有实际变化点的抽象；允许代数数据、纯函数、
  module privacy 与开放 typeclass。


## No Negative Echo

生成最终产物及其包装时，包括标题、文件名、正文、注释、标签、commit、测试
PR 和交付说明，只描述最终采用的状态，假设读者没看过本次会话。

- 会话里的否决、中间尝试和措辞纠正，只当作控制信息，不要让它们成为最终产物的命名或叙述中心。
- 对每个交付面分别判断：不知道本次会话的读者需要这条信息吗？省略会不会导致不准确、不安全、误导或兼容性信息缺失？它是不是任务开始时已提交或用户确认状态中的真实变化，而且当前交付面需要解释它？
- 「不要提 X」不是让你写「无 X」。标题、文件名、开篇和标签应从正向目标重新生成，不要逐词修改被否文案。
- 保留真实的基线变化、已经执行的外部操作，以及必要的技术名称、诊断、测试和快照。任务开始前已有的用户改动不算被否内容。
- 不要把与本任务无关的改动写进本次 commit、PR 或交付说明。对比、引用、审计和迁移说明，只在用户要求或当前交付面确实需要时保留。
- 写完后通读全部用户可见内容及其包装，包括文件名、元数据和 hook 改写。内容发生变化后重新检查，不要另加「已清理」或「无残留」类声明。
