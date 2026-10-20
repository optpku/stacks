/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Cover
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.44.3 (1): a morphism of schemes is finite if and only if some affine open cover of
the target has affine inverse images and induces finite maps on global sections. -/
@[stacks 01WI] #check
  (AlgebraicGeometry.isFinite_iff_exists_affineOpenCover :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.IsFinite f ↔
        ∃ 𝒰 : S.AffineOpenCover.{u},
          ∀ i : 𝒰.I₀,
            AlgebraicGeometry.IsAffine (f ⁻¹ᵁ (𝒰.f i).opensRange) ∧
              (CommRingCat.Hom.hom
                (AlgebraicGeometry.Scheme.Hom.appTop
                  (f ∣_ (𝒰.f i).opensRange))).Finite)

/- Lemma 29.44.3 (2): a morphism of schemes is finite if and only if it is finite after
restriction along every member of some open cover of the target. -/
@[stacks 01WI] #check
  (AlgebraicGeometry.isFinite_iff_exists_openCover :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.IsFinite f ↔
        ∃ 𝒰 : S.OpenCover.{u},
          ∀ i : 𝒰.I₀,
            AlgebraicGeometry.IsFinite (f ∣_ (𝒰.f i).opensRange))

/- Lemma 29.44.3 (3): a finite morphism remains finite after restriction to every open
subscheme of its target. -/
@[stacks 01WI] #check
  (AlgebraicGeometry.IsZariskiLocalAtTarget.restrict
      (P := @AlgebraicGeometry.IsFinite) :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.IsFinite f →
        ∀ U : S.Opens, AlgebraicGeometry.IsFinite (f ∣_ U))
