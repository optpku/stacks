/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay

/-!
# Cohen–Macaulay families of curves

Cohen–Macaulayness is represented by an open of the base of each family of
curves under every cartesian morphism of families. Over a field, it agrees
with Cohen–Macaulayness of the corresponding proper scheme of dimension at
most one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves whose structure morphism is
Cohen–Macaulay. -/
def cohenMacaulay (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.CohenMacaulay (hom P)

/-- Membership in `cohenMacaulay` is Cohen–Macaulayness of the structure morphism. -/
theorem cohenMacaulay_iff {S : Scheme.{u}} (P : Obj S) :
    cohenMacaulay S P ↔ AlgebraicSpace.CohenMacaulay (hom P) :=
  Iff.rfl

/-- Cohen–Macaulayness of families of curves is invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_cohenMacaulay (S : Scheme.{u}) :
    (cohenMacaulay S).IsClosedUnderIsomorphisms :=
  sorry

/-- For every family of curves, an open of its base represents Cohen–Macaulayness
under every cartesian morphism of families. -/
theorem exists_cohenMacaulay_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      cohenMacaulay S Q ↔ Set.range (baseMap φ).left ⊆ U :=
  sorry

/-- The projection of Cohen–Macaulay curve families to their base schemes is
fibred in groupoids. -/
instance instIsFiberedInGroupoids_cohenMacaulay (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((cohenMacaulay S).ι ⋙ p S) :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a
Cohen–Macaulay family of curves if and only if the scheme is Cohen–Macaulay. -/
theorem classifying_factorsThrough_cohenMacaulay_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    cohenMacaulay (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.CohenMacaulay X.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
