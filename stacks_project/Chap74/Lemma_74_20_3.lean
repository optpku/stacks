/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal.Characterization
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

/- Lemma 74.20.3 (1): a morphism has a smooth-local-on-source-and-target property
if and only if every source point lies under a commutative square with smooth
vertical arrows whose top arrow has the property. -/
@[stacks 06FA] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.iff_exists :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∀ x : Points X, existsSmoothSquareAt P f x)

/- Lemma 74.20.3 (2): a morphism has a smooth-local-on-source-and-target property
if and only if the property holds on the top arrow of some commutative square
with smooth vertical arrows whose left vertical arrow is surjective. -/
@[stacks 06FA] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.iff_exists_surjective_square :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔
        ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
          Smooth a ∧ Smooth b ∧ Surjective a ∧ CommSq h a b f ∧ P h)

/- Lemma 74.20.3 (3): a morphism has a smooth-local-on-source-and-target property
if and only if the top arrow of every commutative square with smooth right
vertical arrow and smooth comparison into the fibre product has the property. -/
@[stacks 06FA] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.iff_forall_comparison :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔
        ∀ {U V : AlgebraicSpace S} (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
          (sq : CommSq h a b f),
          Smooth b → Smooth (pullback.lift a h sq.w.symm) → P h)

/- Lemma 74.20.3 (4): a morphism has a smooth-local-on-source-and-target property
if and only if the property holds after base change along every member of some
smooth covering of the target. -/
@[stacks 06FA] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.iff_exists_targetCover :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : (precoverage (@Smooth S)).ZeroHypercover.{u} Y,
        ∀ i : 𝒰.I₀, P (pullback.snd f (𝒰.f i)))

/- Lemma 74.20.3 (5): a morphism has a smooth-local-on-source-and-target property
if and only if every member of some smooth covering of the source has the
property after composition with the morphism. -/
@[stacks 06FA] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.iff_exists_sourceCover :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : (precoverage (@Smooth S)).ZeroHypercover.{u} X,
        ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f))

/- Lemma 74.20.3 (6): a morphism has a smooth-local-on-source-and-target property
if and only if, after some smooth covering of the target, each base change
admits a smooth source covering whose composites to the target-cover member have
the property. -/
@[stacks 06FA] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.iff_exists_targetSourceCovers :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : (precoverage (@Smooth S)).ZeroHypercover.{u} Y, ∀ i : 𝒰.I₀,
        ∃ 𝒱 : (precoverage (@Smooth S)).ZeroHypercover.{u} (pullback f (𝒰.f i)),
          ∀ j : 𝒱.I₀, P (𝒱.f j ≫ pullback.snd f (𝒰.f i)))
