/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Surjectivity is fpqc local on the target

Surjective morphisms of algebraic spaces over a scheme `S` satisfy
`IsLocalAtTarget` for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Surjective

#check (AlgebraicGeometry.AlgebraicSpace.Surjective.isLocalAtTargetFpqc :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsLocalAtTarget
    (@Surjective S : MorphismProperty (AlgebraicSpace S))
    (fpqcPrecoverage S))

variable {S : Scheme.{u}}

#check (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := (@Surjective S : MorphismProperty (AlgebraicSpace S)))
    (K := fpqcPrecoverage S) :
  ∀ {X Y : AlgebraicSpace S} {R : Presieve Y},
    R ∈ (fpqcPrecoverage S).coverings Y → ∀ {f : X ⟶ Y},
      Surjective f ↔
        ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
          R g → Surjective (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace.Surjective
