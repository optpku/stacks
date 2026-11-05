/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Associativity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification
import Lean

/-! The four specified composition comparisons of the compactification tower.
Only their geometric arguments are specialized here. Remaining sheafification,
localization, Kan extension and exactness inputs are exactly the canonical
composition construction's technical parameters. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
noncomputable section
universe u v

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.Associativity

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T] (A : AssocDiagram X g h)

/-- The actual composition comparison for rectangle A. -/
def gammaA :=
  comp.{u, v, v, v, v, v, v} X g (AssocDiagram.compFG X g h A)

/-- The actual composition comparison for rectangle C. -/
def gammaC :=
  @comp.{u, v, v, v, v, v, v} Z T (Over.mk g) h
    (inferInstanceAs (IsSeparated g)) (inferInstanceAs (Scheme.Hom.FiniteType g))
    inferInstance inferInstance
    (inferInstanceAs (CompactSpace Y)) (inferInstanceAs (QuasiSeparatedSpace Y))
    inferInstance inferInstance inferInstance inferInstance (AssocDiagram.compHG X g h A)

/-- The A+B comparison retains its right-associated compactification codomain. -/
def gammaAB :=
  comp.{u, v, v, v, v, v, v} X (g ≫ h) (AssocDiagram.compF X g h A)

/-- The B+C comparison retains its left-associated compactification codomain. -/
def gammaBC :=
  @comp.{u, v, v, v, v, v, v} Z T (Over.mk (X.hom ≫ g)) h
    (inferInstanceAs (IsSeparated (X.hom ≫ g)))
    (inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
    inferInstance inferInstance
    (inferInstanceAs (CompactSpace X.left)) (inferInstanceAs (QuasiSeparatedSpace X.left))
    inferInstance inferInstance inferInstance inferInstance (AssocDiagram.compH X g h A)

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.Associativity
end

@[expose] public section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
noncomputable section
universe u v

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T] (A : AssocDiagram X g h)
  (Λ : Type u) [Ring Λ]

/-- The canonical compactification transition along the first pasting isomorphism. -/
def firstTransition :=
  @isoOfHom.{u, v, v, v, v} Y X Λ inferInstance _ _
    (AssocDiagram.firstCompactificationIso X g h A).inv

/-- The canonical compactification transition along the middle pasting isomorphism. -/
def midTransition :=
  @isoOfHom.{u, v, v, v, v} Z (Over.mk (X.hom ≫ g)) Λ inferInstance _ _
    (AssocDiagram.ofCompositeFG_iso_ofInteriorH X g h A).inv

/-- The canonical compactification transition along the base compactification isomorphism. -/
def baseTransition :=
  @isoOfHom.{u, v, v, v, v} T (Over.mk (g ≫ h)) Λ inferInstance _ _
    (AssocDiagram.baseCompactificationIso X g h A).inv

/-- The canonical compactification transition from the B+C endpoint to the A+B endpoint. -/
def endpointTransition :=
  @isoOfHom.{u, v, v, v, v} T (Over.mk ((X.hom ≫ g) ≫ h)) Λ inferInstance _ _
    (endpointIso X g h A).inv

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity
end

/-! Construct the two canonical routes with shared localization data.

The exact signatures of the four existing comparisons and four explicit geometric
transports determine this telescope. Re-elaborating their expanded source types
exhausts the default heartbeat budget. This bounded elaboration reuses those
already checked expressions and submits the complete definitions to the kernel.
The resulting routes compose the four canonical comparisons with the four
specified compactification transitions. -/

open Lean Meta Elab Command

/-- Bind one coefficient type and one ring structure for dependent module categories. -/
private def withCoefficients (k : Array Expr → MetaM Unit) : MetaM Unit :=
  withLocalDeclD `Λ (mkSort (.succ (.param `u))) fun coefficient =>
    withLocalDecl `instRing .instImplicit
      (mkApp (mkConst ``Ring [.param `u]) coefficient) fun ring =>
      -- Local declaration justification (metaprogramming implementation): the generated
      -- telescope's single Ring supplies inference while its dependent maps are built.
      withNewLocalInstances #[ring] 0 (k #[coefficient, ring])

private def assocName (leaf : Name) : Name :=
  `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity ++ leaf

private def compose (a b : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.CategoryStruct.comp #[a, b]

private def endpoints (map : Expr) : MetaM (Expr × Expr) := do
  let args := (← inferType map).getAppArgs
  unless args.size ≥ 2 do throwError "Not a map"
  return (args[args.size - 2]!, args[args.size - 1]!)

private def unfoldedComp (term : Expr) : MetaM Expr := do
  let actual ← whnf term
  let owner := `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.comp
  unless actual.getAppFn.constName? == some owner do throwError "Not the actual canonical comp"
  let (source, target) ← endpoints actual
  -- Match the equation's left-hand side to the actual boundary functor.
  -- This fixes its dependent arguments, including the chosen localization
  -- data, without inspecting binder names or macro hygiene identifiers.
  let applyEquation (name : Name) (boundary : Expr) : MetaM Expr := do
    let equation ← mkConstWithFreshMVarLevels name
    let (args, _, type) ← forallMetaTelescopeReducing (← inferType equation)
    let some (_, lhs, _) := type.eq? | throwError "Expected a boundary equation"
    unless ← isDefEq lhs boundary do
      throwError "Equation does not describe the actual comparison boundary"
    let result ← instantiateMVars (mkAppN equation args)
    unless !result.hasMVar && !result.hasLevelMVar do
      throwError "Boundary does not determine all equation arguments"
    return result
  let before ← applyEquation
    `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.compDomain_def source
  let after ← applyEquation
    `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.compCodomain_def target
  let before ← mkAppM ``Eq.symm #[before]
  let left ← mkAppM ``CategoryTheory.eqToHom #[before]
  let right ← mkAppM ``CategoryTheory.eqToHom #[after]
  compose (← compose left term) right

private def finishSquare (xs : Array Expr) (values : Array Expr) : MetaM Unit := do
  let a ← unfoldedComp values[0]!
  let c ← unfoldedComp values[1]!
  let ab ← unfoldedComp values[2]!
  let bc ← unfoldedComp values[3]!
  let (aSource, _) ← endpoints a
  let (cSource, hg) ← endpoints c
  let aArgs := aSource.getAppArgs
  let cArgs := cSource.getAppArgs
  unless aSource.getAppFn.constName? == some ``CategoryTheory.Functor.comp &&
      cSource.getAppFn.constName? == some ``CategoryTheory.Functor.comp do
    throwError "Unfolded comparison domains are not actual composite functors"
  let f := aArgs[aArgs.size - 2]!
  let g := aArgs[aArgs.size - 1]!
  let h := cArgs[cArgs.size - 1]!
  unless ← isDefEq g cArgs[cArgs.size - 2]! do throwError "G localization data disagree"
  let assoc ← mkAppM ``CategoryTheory.Functor.associator #[f, g, h]
  let firstHom := values[4]!
  let midHom := values[5]!
  let baseHom := values[6]!
  let endpointInv := values[7]!
  let (_, fab) ← endpoints firstHom
  let mut left ← mkAppM ``CategoryTheory.Iso.hom #[assoc]
  left ← compose left (← mkAppM ``CategoryTheory.Functor.whiskerLeft #[f, c])
  left ← compose left (← mkAppM ``CategoryTheory.Functor.whiskerRight #[firstHom, hg])
  left ← compose left (← mkAppM ``CategoryTheory.Functor.whiskerLeft #[fab, baseHom])
  left ← compose left ab
  let mut right ← mkAppM ``CategoryTheory.Functor.whiskerRight #[a, h]
  right ← compose right (← mkAppM ``CategoryTheory.Functor.whiskerRight #[midHom, h])
  right ← compose right bc
  right ← compose right endpointInv
  unless ← isDefEq (← inferType left) (← inferType right) do
    throwError "The two actual paths still have different types"
  -- Pin the exact same codomain spelling for both definitions. Their bodies
  -- and the kernel's type check are unchanged; consumers need not repeat a
  -- deep conversion of two definitionally equal dependent signatures.
  let commonType ← mkForallFVars xs (← inferType left)
  for (name, term) in [(assocName `leftPath, left), (assocName `rightPath, right)] do
    let type := commonType
    let value ← mkLambdaFVars xs term
    unless !type.hasMVar && !value.hasMVar do throwError "Unresolved path metavariable"
    addDecl <| Declaration.defnDecl {
      name := name, levelParams := [`u, `v], type := type, value := value,
      hints := .regular 0, safety := .safe }
    addDocStringCore name (if name == assocName `leftPath then
      "The upper and right composition route through the canonical comparisons and compactification transitions." else
      "The left and lower composition route through the canonical comparisons and compactification transitions.")

run_cmd liftTermElabM do
  let geometry ← getConstInfo
    `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity.endpointIso
  forallTelescope geometry.type fun geometricArgs _ => withCoefficients fun coefficientArgs => do
    let fixedArgs := geometricArgs ++ coefficientArgs
    let names := (#[`gammaA, `gammaC, `gammaAB, `gammaBC].map
      (`AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.Associativity ++ ·)) ++
      (#[`firstTransition, `midTransition, `baseTransition, `endpointTransition].map assocName)
    let rec next (remaining : List Name) (pool values : Array Expr) : MetaM Unit := do
      match remaining with
      | [] => finishSquare pool values
      | name :: rest =>
        let info ← getConstInfo name
        let levels := info.levelParams.map fun p => if p == `u then Level.param `u else Level.param `v
        -- The diagram's type determines X, g, h and their source/target schemes.
        -- Match that explicit data before supplying the geometric Prop instances;
        -- their order in the eight comparison telescopes need not agree.
        let diagram := geometricArgs.back!
        let rec specialize (fuel : Nat) (type value : Expr)
            (args : Array Expr) : MetaM (Expr × Expr) := do
          let fuel + 1 := fuel | throwError "Comparison diagram binder absent"
          let .forallE _ domain body _ := type | throwError "Comparison diagram binder absent"
          if domain.getAppFn.constName? == some ``AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram then
            unless ← isDefEq domain (← inferType diagram) do
              throwError "Comparison has a different compactification diagram"
            for arg in args do
              let arg ← instantiateMVars arg
              if arg.isMVar then
                let requirement ← instantiateMVars (← inferType arg)
                unless !requirement.hasMVar && (← isProp requirement) do
                  throwError "Diagram does not determine the comparison's geometric data"
                let mut supplied := false
                for x in geometricArgs do
                  if ← isDefEq (← inferType x) requirement then
                    unless ← isDefEq arg x do throwError "Geometric instance mismatch"
                    supplied := true
                    break
                unless supplied do throwError "Missing geometric premise"
            return (← instantiateMVars (body.instantiate1 diagram),
              ← instantiateMVars (mkApp value diagram))
          else
            let arg ← mkFreshExprMVar domain
            specialize fuel (body.instantiate1 arg) (mkApp value arg) (args.push arg)
        let (type, value) ← specialize 64
          (info.type.instantiateLevelParams info.levelParams levels) (mkConst name levels) #[]
        let mut type := type
        let mut value := value
        for x in coefficientArgs do
          let .forallE _ domain body _ := type | throwError "Coefficient binder absent"
          unless ← isDefEq (← inferType x) domain do throwError "Coefficient type mismatch"
          type := body.instantiate1 x
          value := mkApp value x
        let rec bind (fuel : Nat) (type value : Expr) (pool : Array Expr) : MetaM Unit := do
          let fuel + 1 := fuel | throwError "Bounded shared telescope exhausted"
          match type with
          | .forallE n domain body bi =>
            let proofOnly ← isProp domain
            let mut chosen := none
            for x in pool do
              let d ← x.fvarId!.getDecl
              if bi.isInstImplicit && d.binderInfo.isInstImplicit &&
                  d.type.getAppFn.constName? == domain.getAppFn.constName? then
                -- Proof irrelevance identifies repeated proof-only requirements.
                -- Data-bearing instances share the exact same value only when
                -- their types are definitionally equal.
                let same ← if d.type == domain then pure true else
                  if proofOnly then pure false else isDefEq d.type domain
                if same then
                  chosen := some x
                  break
            if let some x := chosen then
              unless ← isDefEq (← inferType x) domain do throwError "Shared binder mismatch {n}"
              bind fuel (body.instantiate1 x) (mkApp value x) pool
            else
              -- Temporary elaborator context: an instance binder must be registered
              -- while its dependent functor and localization expressions are constructed.
              -- The exported declaration retains it as an explicit telescope parameter.
              withLocalDecl n bi domain fun x =>
                withNewLocalInstances #[x] 0 <|
                  bind fuel (body.instantiate1 x) (mkApp value x) (pool.push x)
          | _ =>
            next rest pool (values.push value)
        bind 256 type value pool
    next names.toList fixedArgs #[]

/-! The four-arrow square with canonical transitions between compactifications. -/

@[expose] public section
universe u v
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

/-- The two canonical composition routes agree as families of natural transformations. -/
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
    addDocStringCore (owner ++ `comp_assoc)
      "The canonical lower-shriek composition square commutes for each compatible compactification tower and coefficient ring."
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
      addDocStringCore (owner ++ `comp_assoc_app)
        "The components of the canonical lower-shriek composition square agree at every derived object."
