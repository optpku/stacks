/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal

/-!
# Descent of étale-local morphism properties

A scheme-morphism property that is étale local on source-and-target may be
tested on a single surjective étale scheme square. On represented spaces this
recovers the underlying scheme property. For representable morphisms it agrees
with the represented-pullback property under base-change stability and fppf
locality on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a commutative square with étale vertical arrows from schemes,
surjective source atlas, and top arrow satisfying `P`. -/
def etaleLocal.existsSurjectiveSquare {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = yoneda.map h ≫ b ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a ∧
            P h.left

/-- For a scheme-morphism property étale local on source-and-target, its
étale-local lift holds exactly when some commutative étale scheme square with
surjective source atlas has top arrow satisfying the property. -/
theorem etaleLocal_iff_existsSurjectiveSquare {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleLocal P f ↔ etaleLocal.existsSurjectiveSquare P f :=
  sorry

/-- For a scheme-morphism property étale local on source-and-target, its
étale-local lift on a morphism between represented algebraic spaces agrees
with the property of the underlying scheme morphism. -/
theorem etaleLocal_ofOverMap_iff {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {U V : Over S} (h : U ⟶ V) :
    etaleLocal P (X := ofOver U) (Y := ofOver V) (yoneda.map h) ↔ P h.left :=
  sorry

/-- For a scheme-morphism property étale local on source-and-target, stable
under arbitrary base change, and fppf local on the target, its étale-local lift
on a representable morphism agrees with its represented-pullback property. -/
theorem etaleLocal_iff_over_presheaf {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    etaleLocal P f ↔ (over P).presheaf f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
