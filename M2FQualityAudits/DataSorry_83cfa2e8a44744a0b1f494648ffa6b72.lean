module

import Lean

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
public import stacks_project.Chap53.Example_53_23_1_Contracting_a_rational_tail

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.RationalTail

/-- The scheme over `K` obtained as the coproduct of the component schemes of a family of
rational tails on the base change of `X` to `K`. -/
noncomputable def componentCoproduct
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k)
    {ι : Type u}
    (tails : ι → RationalTail (FieldExtension.Over.baseChange k K X)) :
    SchemeOverField K :=
  Over.mk (Limits.Sigma.desc fun i : ι ↦
    (componentOver (FieldExtension.Over.baseChange k K X) (tails i).component).hom)

/-- The structure morphism of `componentCoproduct` is the Sigma coproduct of the component
morphisms of the tail family. -/
theorem componentCoproduct_hom
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k)
    {ι : Type u}
    (tails : ι → RationalTail (FieldExtension.Over.baseChange k K X)) :
    (componentCoproduct K X tails).hom =
      Limits.Sigma.desc fun i : ι ↦
        (componentOver (FieldExtension.Over.baseChange k K X) (tails i).component).hom := sorry

/-- The canonical morphism from the coproduct of the summand components into the base-changed
scheme `X_K`. -/
noncomputable def componentCoproductMap
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k)
    {ι : Type u}
    (tails : ι → RationalTail (FieldExtension.Over.baseChange k K X)) :
    (componentCoproduct K X tails).left ⟶
      (FieldExtension.Over.baseChange k K X).left :=
  Limits.Sigma.desc fun i : ι ↦
    (FieldExtension.Over.baseChange k K X).left.irreducibleComponentSubschemeι
      (tails i).component

/-- The coproduct-to-`X_K` morphism is the Sigma descent of the component inclusions. -/
theorem componentCoproductMap_spec
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k)
    {ι : Type u}
    (tails : ι → RationalTail (FieldExtension.Over.baseChange k K X)) :
    componentCoproductMap K X tails =
      Limits.Sigma.desc fun i : ι ↦
        (FieldExtension.Over.baseChange k K X).left.irreducibleComponentSubschemeι
          (tails i).component := sorry

/-- The inclusion of the selected component after base change to `K`. -/
noncomputable def baseChangeComponentMap
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) (C : RationalTail X) :
    (FieldExtension.Over.baseChange k K (componentOver X C.component)).left ⟶
      (FieldExtension.Over.baseChange k K X).left :=
  ((FieldExtension.Over.functor k K).map
    (Over.homMk (X.left.irreducibleComponentSubschemeι C.component) :
      componentOver X C.component ⟶ X)).left

/-- The selected-component map is obtained by applying field-extension base change to its
canonical inclusion into `X`. -/
theorem baseChangeComponentMap_spec
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) (C : RationalTail X) :
    baseChangeComponentMap K X C =
      ((FieldExtension.Over.functor k K).map
        (Over.homMk (X.left.irreducibleComponentSubschemeι C.component) :
          componentOver X C.component ⟶ X)).left := sorry

/-- Explicit finite coproduct data for the base change of a rational-tail component. -/
structure BaseChangeDecomposition
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) (C : RationalTail X) where
  /-- The finite indexing type of the rational-tail summands. -/
  ι : Type u
  /-- Finiteness of the indexing type. -/
  finite : Finite ι
  /-- The rational tails appearing as summands after base change to `K`. -/
  tails : ι → RationalTail (FieldExtension.Over.baseChange k K X)
  /-- Every summand lies in the component fibre of the selected tail component. -/
  component_fiber :
    ∀ i : ι,
      FieldExtension.Irreducible.componentsMap k K X.hom (tails i).component = C.component
  /-- An isomorphism from the base-changed component to the displayed coproduct. -/
  iso :
    FieldExtension.Over.baseChange k K (componentOver X C.component) ≅
      componentCoproduct K X tails
  /-- The coproduct presentation agrees with the canonical inclusion into `X_K`. -/
  ambient_map_commutes :
    iso.hom.left ≫ componentCoproductMap K X tails = baseChangeComponentMap K X C

namespace BaseChangeDecomposition

/-- Construct a finite coproduct decomposition from its explicit index, family, and isomorphism.
-/
def of
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) (C : RationalTail X)
    (ι : Type u) (finite : Finite ι)
    (tails : ι → RationalTail (FieldExtension.Over.baseChange k K X))
    (component_fiber :
      ∀ i : ι,
        FieldExtension.Irreducible.componentsMap k K X.hom (tails i).component = C.component)
    (iso :
      FieldExtension.Over.baseChange k K (componentOver X C.component) ≅
        componentCoproduct K X tails)
    (ambient_map_commutes :
      iso.hom.left ≫ componentCoproductMap K X tails = baseChangeComponentMap K X C) :
    BaseChangeDecomposition K X C :=
  { ι := ι
    finite := finite
    tails := tails
    component_fiber := component_fiber
    iso := iso
    ambient_map_commutes := ambient_map_commutes }

/-- The specification of a decomposition records finiteness and its coproduct presentation. -/
theorem spec
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {X : SchemeOverField k} {C : RationalTail X}
    (D : BaseChangeDecomposition K X C) :
    Finite D.ι ∧
      (∀ i : D.ι,
        FieldExtension.Irreducible.componentsMap k K X.hom (D.tails i).component = C.component) ∧
      Nonempty
        (FieldExtension.Over.baseChange k K (componentOver X C.component) ≅
          componentCoproduct K X D.tails) ∧
      D.iso.hom.left ≫ componentCoproductMap K X D.tails = baseChangeComponentMap K X C := sorry

end BaseChangeDecomposition

end AlgebraicGeometry.SchemeOverField.RationalTail


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
