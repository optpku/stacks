/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail

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

/-- Construct a finite coproduct decomposition from its explicit index, family, and isomorphism. -/
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

/-- Every rational tail on a proper one-dimensional nodal scheme over `k` becomes a finite
coproduct of rational tails after arbitrary field extension. -/
theorem baseChange_decomposition
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (C : RationalTail X) :
    Nonempty (RationalTail.BaseChangeDecomposition K X C) := sorry

end AlgebraicGeometry.SchemeOverField.RationalTail
