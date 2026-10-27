/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Global
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein

/-!
# Gorenstein families of curves

Gorensteinness is represented by an open of the base of each family of curves
under every cartesian morphism of families. Over a field, it agrees with
Gorensteinness of the corresponding proper scheme of dimension at most one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves whose structure morphism is
Gorenstein. -/
def gorenstein (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Gorenstein (hom P)

/-- Membership in `gorenstein` is Gorensteinness of the structure morphism. -/
theorem gorenstein_iff {S : Scheme.{u}} (P : Obj S) :
    gorenstein S P ↔ AlgebraicSpace.Gorenstein (hom P) :=
  Iff.rfl

/-- Gorensteinness of families of curves is invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_gorenstein (S : Scheme.{u}) :
    (gorenstein S).IsClosedUnderIsomorphisms :=
  sorry

/-- For every family of curves, an open of its base represents Gorensteinness
under every cartesian morphism of families. -/
theorem exists_gorenstein_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      gorenstein S Q ↔ Set.range (baseMap φ).left ⊆ U :=
  sorry

/-- The projection of Gorenstein curve families to their base schemes is fibred
in groupoids. -/
instance instIsFiberedInGroupoids_gorenstein (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((gorenstein S).ι ⋙ p S) :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a Gorenstein
family of curves if and only if the scheme is Gorenstein. -/
theorem classifying_factorsThrough_gorenstein_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    gorenstein (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.Gorenstein X.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
