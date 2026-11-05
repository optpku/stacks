import Lean
import AnnalsChallenge.AnnalsOfMathematics.«2021-194-1-UniformMordellLang»

universe u

noncomputable section

/- The audit visits transitive dependencies, including opaque theorem bodies,
   and classifies the TYPE of each sorry under its binder context.
   Proof holes are permitted; data holes cause compilation to fail. -/
open Lean Elab Command Meta

partial def auditHoles (e : Expr) : MetaM (Array (Bool × String)) := do
  if e.isAppOf ``sorryAx then
    let ty := e.getAppArgs[0]!
    return #[(← isProp ty, (← ppExpr ty).pretty)]
  match e with
  | .lam n ty b bi | .forallE n ty b bi =>
    let a ← auditHoles ty
    let b ← withLocalDecl n bi ty fun x => auditHoles (b.instantiate1 x)
    return a ++ b
  | .letE n ty v b _ =>
    let a ← auditHoles ty
    let c ← auditHoles v
    let b ← withLetDecl n ty v fun x => auditHoles (b.instantiate1 x)
    return a ++ c ++ b
  | .app f a => return (← auditHoles f) ++ (← auditHoles a)
  | .mdata _ b | .proj _ _ b => auditHoles b
  | _ => return #[]

elab "#assert_no_data_sorries " id:ident : command => do
  let env ← getEnv
  if (env.find? id.getId).isNone then
    throwError m!"Unknown audit root: {id.getId}"
  let mut todo := #[id.getId]
  let mut seen : NameSet := {}
  let mut proofDecls : Nat := 0
  let mut dataDecls : Nat := 0
  let mut dataHoles : Nat := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let deps := ci.type.getUsedConstants ++
        ((ci.value? true).map Expr.getUsedConstants |>.getD #[])
      if deps.contains ``sorryAx then
        let holes ← liftTermElabM do
          let a ← auditHoles ci.type
          let b ← match ci.value? true with
            | some e => auditHoles e
            | none => pure #[]
          return a ++ b
        let ds := holes.filter fun h => !h.1
        if ds.isEmpty then proofDecls := proofDecls + 1
        else
          dataDecls := dataDecls + 1
          dataHoles := dataHoles + ds.size
          logInfo m!"DATA {n}: {ds}"
      todo := todo ++ deps
  if dataHoles != 0 then
    throwError m!"Reachable non-Prop sorry holes: {dataHoles}"
  logInfo m!"CENSUS {id.getId}: visited={seen.size}; proofOnlyDeclarations={proofDecls}; dataDeclarations={dataDecls}; dataHoles={dataHoles}"



#assert_no_data_sorries AlgebraicGeometry.JacobianChallenge.genus
#assert_no_data_sorries AlgebraicGeometry.JacobianChallenge.Jacobian
#assert_no_data_sorries AlgebraicGeometry.JacobianChallenge.Jacobian.instGrpObj
#assert_no_data_sorries AlgebraicGeometry.JacobianChallenge.Jacobian.ofCurve
#assert_no_data_sorries UniformMordellLang.c
#assert_no_data_sorries UniformMordellLang.theorem_1_1

#print axioms AlgebraicGeometry.JacobianChallenge.genus
#check AlgebraicGeometry.JacobianChallenge.Jacobian.comp_ofCurve
#check AlgebraicGeometry.JacobianChallenge.Jacobian.exists_unique_ofCurve_comp
#check UniformMordellLang.one_le_c
#check UniformMordellLang.c_min
#check UniformMordellLang.theorem_1_1_exists

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.JacobianChallenge

-- Exact original assumptions, with no algebraic-closure or chosen-point restriction.
example {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] : GrpObj (Jacobian C) := inferInstance

example {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : C ⟶ Jacobian C :=
  Jacobian.ofCurve P

example (g d : ℕ) : 1 ≤ UniformMordellLang.c g d :=
  UniformMordellLang.one_le_c g d
