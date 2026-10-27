/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.CohenMacaulay
public import ReasLib.Topology.KrullDimension.Equidimensional

/-!
# Cohen–Macaulay families of curves of relative dimension one

Cohen–Macaulayness together with exact relative dimension one is represented
by an open of the base of each family of curves under every cartesian morphism
of families. Over a field, this characterizes proper nonempty Cohen–Macaulay
schemes that are equidimensional of dimension one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves whose structure morphism is
Cohen–Macaulay of exact relative dimension one. -/
def cohenMacaulayDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.CohenMacaulay (hom P) ∧ RelativeDimension (hom P) 1

/-- Membership in `cohenMacaulayDim1` is Cohen–Macaulayness of the structure
morphism together with exact relative dimension one. -/
theorem cohenMacaulayDim1_iff {S : Scheme.{u}} (P : Obj S) :
    cohenMacaulayDim1 S P ↔
      AlgebraicSpace.CohenMacaulay (hom P) ∧ RelativeDimension (hom P) 1 :=
  Iff.rfl

/-- Cohen–Macaulayness and exact relative dimension one of families of curves
are invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_cohenMacaulayDim1 (S : Scheme.{u}) :
    (cohenMacaulayDim1 S).IsClosedUnderIsomorphisms :=
  sorry

/-- Every Cohen–Macaulay family of curves of exact relative dimension one is
a Cohen–Macaulay family of curves. -/
theorem cohenMacaulayDim1_le_cohenMacaulay {S : Scheme.{u}} (P : Obj S) :
    cohenMacaulayDim1 S P → cohenMacaulay S P :=
  fun h => h.1

/-- For every family of curves, an open of its base represents Cohen–Macaulayness
and exact relative dimension one under every cartesian morphism of families. -/
theorem exists_cohenMacaulayDim1_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      cohenMacaulayDim1 S Q ↔ Set.range (baseMap φ).left ⊆ U :=
  sorry

/-- The projection of Cohen–Macaulay curve families of exact relative dimension
one to their base schemes is fibred in groupoids. -/
instance instIsFiberedInGroupoids_cohenMacaulayDim1 (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((cohenMacaulayDim1 S).ι ⋙ p S) :=
  sorry

/-- A proper nonempty scheme of dimension at most one over a field defines a
Cohen–Macaulay family of curves of exact relative dimension one if and only if
it is Cohen–Macaulay and equidimensional of dimension one. -/
theorem classifying_factorsThrough_cohenMacaulayDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    cohenMacaulayDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.CohenMacaulay X.left ∧ EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
