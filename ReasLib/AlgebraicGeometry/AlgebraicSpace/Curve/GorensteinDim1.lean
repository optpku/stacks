/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Gorenstein
public import ReasLib.Topology.KrullDimension.Equidimensional

/-!
# Gorenstein families of curves of relative dimension one

Gorensteinness together with exact relative dimension one is represented by an
open of the base of each family of curves under every cartesian morphism of
families. Over a field, this characterizes proper nonempty Gorenstein schemes
that are equidimensional of dimension one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves whose structure morphism is
Gorenstein of exact relative dimension one. -/
def gorensteinDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Gorenstein (hom P) ∧ RelativeDimension (hom P) 1

/-- Membership in `gorensteinDim1` is Gorensteinness of the structure morphism
together with exact relative dimension one. -/
theorem gorensteinDim1_iff {S : Scheme.{u}} (P : Obj S) :
    gorensteinDim1 S P ↔
      AlgebraicSpace.Gorenstein (hom P) ∧ RelativeDimension (hom P) 1 :=
  Iff.rfl

/-- Gorensteinness and exact relative dimension one of families of curves are
invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_gorensteinDim1 (S : Scheme.{u}) :
    (gorensteinDim1 S).IsClosedUnderIsomorphisms :=
  sorry

/-- Every Gorenstein family of curves of exact relative dimension one is a
Gorenstein family of curves. -/
theorem gorensteinDim1_le_gorenstein {S : Scheme.{u}} (P : Obj S) :
    gorensteinDim1 S P → gorenstein S P :=
  fun h => h.1

/-- For every family of curves, an open of its base represents Gorensteinness
and exact relative dimension one under every cartesian morphism of families. -/
theorem exists_gorensteinDim1_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      gorensteinDim1 S Q ↔ Set.range (baseMap φ).left ⊆ U :=
  sorry

/-- The projection of Gorenstein curve families of exact relative dimension one
to their base schemes is fibred in groupoids. -/
instance instIsFiberedInGroupoids_gorensteinDim1 (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((gorensteinDim1 S).ι ⋙ p S) :=
  sorry

/-- A proper nonempty scheme of dimension at most one over a field defines a
Gorenstein family of curves of exact relative dimension one if and only if it
is Gorenstein and equidimensional of dimension one. -/
theorem classifying_factorsThrough_gorensteinDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    gorensteinDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.Gorenstein X.left ∧ EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
