module

public import stacks_project.Chap63.Lemma_63_9_3_CanonicalRoutes
import Lean

/-! The canonical four-arrow square, using the63.9.1 transitions for the
specified geometric compactification isomorphisms. -/

@[expose] public section
universe u v
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

/-- Associativity of the actual four composition comparisons, including the
canonical compactification transitions. The Statement proof obligation is
unchanged; the data defining both routes is explicit and kernel checked. -/
theorem comp_assoc_function :
    @CanonicalAssociativity.leftPath.{u, v} =
      @CanonicalAssociativity.rightPath.{u, v} := sorry

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

open Lean Meta Elab Command

private def explicitTelescope (type : Expr)
    (k : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  let mut context ← getLCtx
  let mut xs := #[]
  let mut rest := type
  for _ in [:512] do
    match rest with
    | .forallE n domain body bi =>
      let id ← mkFreshFVarId
      context := context.mkLocalDecl id n (domain.instantiateRev xs) bi
      xs := xs.push (mkFVar id)
      rest := body
    | _ => return ← withLCtx context (← getLocalInstances) (k xs (rest.instantiateRev xs))
  throwError "POINTWISE_TELESCOPE_BOUND"

run_cmd liftTermElabM do
  let owner := `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek
  let info ← getConstInfo (owner ++ `comp_assoc_function)
  let h := mkConst info.name (info.levelParams.map Level.param)
  let eqArgs := info.type.getAppArgs
  unless info.type.isAppOf ``Eq && eqArgs.size == 3 do throwError "NOT_ROUTE_EQUALITY"
  let routeType := eqArgs[0]!
  let left := eqArgs[1]!
  let right := eqArgs[2]!
  let level := info.type.getAppFn.constLevels!.head!
  explicitTelescope routeType fun xs resultType => do
    let leftValue := mkAppN left xs
    let rightValue := mkAppN right xs
    let target ← mkEq leftValue rightValue
    let resultLevel := target.getAppFn.constLevels!.head!
    let evaluator ← withLocalDeclD `route routeType fun route =>
      mkLambdaFVars #[route] (mkAppN route xs)
    let proof := mkApp6 (mkConst ``congrArg [level, resultLevel])
      routeType resultType left right evaluator h
    let type ← mkForallFVars xs target
    let value ← mkLambdaFVars xs proof
    unless !type.hasMVar && !value.hasMVar && !type.hasFVar && !value.hasFVar do
      throwError "UNRESOLVED_POINTWISE_EXPORT"
    addDecl <| .thmDecl {
      name := owner ++ `comp_assoc
      levelParams := info.levelParams
      type := type
      value := value }
    let leftApp ← mkAppM ``CategoryTheory.NatTrans.app #[leftValue]
    let .forallE _ objectType _ _ ← inferType leftApp | throwError "NOT_COMPONENT_FUNCTION"
    withLocalDeclD `K objectType fun object => do
      let componentLeft := mkApp leftApp object
      let componentRight ← mkAppM ``CategoryTheory.NatTrans.app #[rightValue, object]
      let componentGoal ← mkEq componentLeft componentRight
      let componentLevel := componentGoal.getAppFn.constLevels!.head!
      let componentType ← inferType componentLeft
      let componentEvaluator ← withLocalDeclD `map resultType fun map => do
        mkLambdaFVars #[map] (← mkAppM ``CategoryTheory.NatTrans.app #[map, object])
      let componentProof := mkApp6 (mkConst ``congrArg [resultLevel, componentLevel])
        resultType componentType leftValue rightValue componentEvaluator proof
      let type ← mkForallFVars (xs.push object) componentGoal
      let value ← mkLambdaFVars (xs.push object) componentProof
      addDecl <| .thmDecl {
        name := owner ++ `comp_assoc_app
        levelParams := info.levelParams
        type := type
        value := value }
    logInfo m!"POINTWISE_AND_OBJECTWISE_EXPORT_PASS {xs.size}"
