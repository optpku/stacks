/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

/- Lemma 74.21.3 (1): a morphism has an étale-smooth-local-on-source-and-target
property if and only if every source point lies under a commutative square with
smooth right vertical arrow, étale comparison into the fibre product, and top
arrow of the property. -/
@[stacks 0CG1] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.iff_exists :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∀ x : Points X, existsEtaleSmoothSquareAt P f x)

/- Lemma 74.21.3 (2): a morphism has an étale-smooth-local-on-source-and-target
property if and only if the property holds on the top arrow of some commutative
square with smooth right vertical arrow, étale comparison into the fibre
product, and surjective left vertical arrow. -/
@[stacks 0CG1] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.iff_exists_surjective_square :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔
        ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
          (sq : CommSq h a b f),
            Smooth b ∧ Etale (etaleSmoothSquareLift sq) ∧ Surjective a ∧ P h)

/- Lemma 74.21.3 (3): a morphism has an étale-smooth-local-on-source-and-target
property if and only if the top arrow of every commutative square with smooth
right vertical arrow and étale comparison into the fibre product has the
property. -/
@[stacks 0CG1] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.iff_forall_comparison :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔
        ∀ {U V : AlgebraicSpace S} (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
          (sq : CommSq h a b f),
          Smooth b → Etale (etaleSmoothSquareLift sq) → P h)

/- Lemma 74.21.3 (4): a morphism has an étale-smooth-local-on-source-and-target
property if and only if the property holds after base change along every member
of some smooth covering of the target. -/
@[stacks 0CG1] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.iff_exists_targetCover :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : (smoothPrecoverage S).ZeroHypercover.{u} Y,
        ∀ i : 𝒰.I₀, P (pullback.snd f (𝒰.f i)))

/- Lemma 74.21.3 (5): a morphism has an étale-smooth-local-on-source-and-target
property if and only if every member of some étale covering of the source has
the property after composition with the morphism. -/
@[stacks 0CG1] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.iff_exists_sourceCover :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : (@etalePrecoverage S).ZeroHypercover.{u} X,
        ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f))

/- Lemma 74.21.3 (6): a morphism has an étale-smooth-local-on-source-and-target
property if and only if, after some smooth covering of the target, each base
change admits an étale source covering whose composites to the target-cover
member have the property. -/
@[stacks 0CG1] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.iff_exists_targetSourceCovers :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : (smoothPrecoverage S).ZeroHypercover.{u} Y, ∀ i : 𝒰.I₀,
        ∃ 𝒱 : (@etalePrecoverage S).ZeroHypercover.{u} (pullback f (𝒰.f i)),
          ∀ j : 𝒱.I₀, P (𝒱.f j ≫ pullback.snd f (𝒰.f i)))
