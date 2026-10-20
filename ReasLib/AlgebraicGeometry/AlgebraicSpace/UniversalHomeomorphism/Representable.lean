/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

/-!
# Representable universal homeomorphisms of algebraic spaces

A representable morphism of algebraic spaces is a universal homeomorphism exactly
when its represented scheme pullbacks are universal homeomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A representable morphism of algebraic spaces is a universal homeomorphism
exactly when all represented scheme pullbacks are universal homeomorphisms. -/
theorem universalHomeomorphism_presheaf_iff_universalHomeomorphism
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversalHomeomorphism : MorphismProperty Scheme.{u})).presheaf f ↔
      UniversalHomeomorphism f :=
  sorry

/-- A represented scheme universal-homeomorphism property implies the corresponding
algebraic-space morphism is a universal homeomorphism. -/
theorem universalHomeomorphism_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.UniversalHomeomorphism :
      MorphismProperty Scheme.{u})).presheaf f) :
    UniversalHomeomorphism f :=
  (universalHomeomorphism_presheaf_iff_universalHomeomorphism hf).mp h

/-- An algebraic-space universal homeomorphism has the represented scheme
universal-homeomorphism property. -/
theorem universalHomeomorphism_presheaf_of_universalHomeomorphism
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversalHomeomorphism f) :
    (over (@AlgebraicGeometry.UniversalHomeomorphism : MorphismProperty Scheme.{u})).presheaf f :=
  (universalHomeomorphism_presheaf_iff_universalHomeomorphism hf).mpr h

/-- For a representable morphism, the represented scheme criterion is equivalent to
being a homeomorphism on points after every algebraic-space pullback. -/
theorem universalHomeomorphism_presheaf_iff_pointsIsHomeomorph_of_isPullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversalHomeomorphism : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → pointsIsHomeomorph pZ := by
  rw [universalHomeomorphism_presheaf_iff_universalHomeomorphism hf]
  constructor
  · intro h Z P g pZ pX sq
    exact h.universally_isHomeomorph pX g pZ sq
  · intro h
    exact ⟨fun Z P g pZ pX sq => h sq⟩

end AlgebraicGeometry.AlgebraicSpace
