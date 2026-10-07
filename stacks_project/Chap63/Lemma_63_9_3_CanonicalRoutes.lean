module

public import stacks_project.Chap63.Lemma_63_9_3_Comparisons
public import stacks_project.Chap63.Lemma_63_9_3_CanonicalTransitions
import Lean

/-! Construct the two canonical routes with shared localization data.

The exact signatures of the four existing comparisons and four explicit geometric
transports determine this telescope. Re-elaborating their expanded source types
exhausts the default heartbeat budget. This bounded elaboration reuses those
already checked expressions and submits the complete definitions to the kernel.
No axiom, placeholder, arbitrary comparison binder or runtime IO is introduced. -/

open Lean Meta Elab Command

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
  let args := actual.getAppArgs
  let mut type := (← getConstInfo owner).type
  let mut bindings := []
  for arg in args do
    let .forallE name _ rest _ := type | throwError "Parent comp telescope changed"
    bindings := (name, arg) :: bindings
    type := rest
  -- The irreducible_def equations expose more explicit arguments than comp.
  -- Reuse its exact argument expressions rather than asking typeclass search
  -- to choose a new localization while unfolding the boundary functors.
  let applyEquation (name : Name) : MetaM Expr := do
    let info ← getConstInfo name
    -- Macro-generated equation universes are renamed too. Infer them from
    -- the exact arguments; do not identify unrelated levels by their names.
    let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
    let mut equationType := info.type.instantiateLevelParams info.levelParams levels
    let mut value := mkConst name levels
    for _ in [:256] do
      match equationType with
      | .forallE n domain body _ =>
        let mut selected := bindings.lookup n
        if selected.isNone && n.toString.startsWith "inst." then
          -- irreducible_def clones the macro hygiene prefix, while retaining
          -- the original binder's final hygiene index. Require a unique match
          -- and then verify the full instantiated type before using it.
          let key := (n.toString.splitOn "._hyg.").getLast!
          let candidates := bindings.filter fun (old, _) =>
            old.toString.startsWith "inst." && (old.toString.splitOn "._hyg.").getLast! == key
          if candidates.length == 1 then selected := some candidates.head!.2
        let some arg := selected | throwError "Equation binder absent from comp: {n}"
        unless ← isDefEq domain (← inferType arg) do
          throwError "Equation binder type mismatch: {n}"
        equationType := body.instantiate1 arg
        value := mkApp value arg
      | _ =>
        let result ← instantiateMVars value
        unless !result.hasMVar && !result.hasLevelMVar do
          throwError "Unresolved equation universe or expression metavariable"
        return result
    throwError "Equation telescope exceeds bound"
  let before ← applyEquation `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.compDomain_def
  let after ← applyEquation `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.compCodomain_def
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

run_cmd liftTermElabM do
  let geometry ← getConstInfo
    `AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram.endpointAmbientIso
  forallTelescope geometry.type fun geometricArgs _ => do
    let mut fixed := []
    for x in geometricArgs do fixed := ((← x.fvarId!.getDecl).userName, x) :: fixed
    let names := (#[`gammaA, `gammaC, `gammaAB, `gammaBC].map
      (`AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.Associativity ++ ·)) ++
      (#[`firstTransition, `midTransition, `baseTransition, `endpointTransition].map assocName)
    let rec next (remaining : List Name) (pool values : Array Expr) : MetaM Unit := do
      match remaining with
      | [] => finishSquare pool values
      | name :: rest =>
        let info ← getConstInfo name
        let levels := info.levelParams.map fun p => if p == `u then Level.param `u else Level.param `v
        let rec bind (fuel : Nat) (type value : Expr) (pool : Array Expr) : MetaM Unit := do
          let fuel + 1 := fuel | throwError "Bounded shared telescope exhausted"
          match type with
          | .forallE n domain body bi =>
            let proofOnly ← isProp domain
            let mut chosen := fixed.lookup n
            if chosen.isNone then
              for x in pool do
                let d ← x.fvarId!.getDecl
                if (bi.isInstImplicit && d.binderInfo.isInstImplicit &&
                    d.type.getAppFn.constName? == domain.getAppFn.constName?) ||
                    (n == `Λ && d.userName == n) then
                  -- Equal proof-only requirements may be repeated: proof
                  -- irrelevance already identifies their evidence. Deeply
                  -- reducing whole functors to deduplicate these proofs was
                  -- the measured bottleneck. Data-bearing instances still
                  -- share the exact same value under definitional equality.
                  let same ← if d.type == domain then pure true else
                    if proofOnly then pure false else isDefEq d.type domain
                  if same then
                    chosen := some x
                    break
            if let some x := chosen then
              unless ← isDefEq (← inferType x) domain do throwError "Shared binder mismatch {n}"
              bind fuel (body.instantiate1 x) (mkApp value x) pool
            else
              withLocalDecl n bi domain fun x =>
                withNewLocalInstances #[x] 0 <|
                  bind fuel (body.instantiate1 x) (mkApp value x) (pool.push x)
          | _ =>
            next rest pool (values.push value)
        bind 256 (info.type.instantiateLevelParams info.levelParams levels)
          (mkConst name levels) pool
    next names.toList geometricArgs #[]

