/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Definition 29.43.1 (1): a scheme morphism is projective exactly when it admits a
closed-immersion presentation in the projective bundle of a finite-type quasicoherent module. -/
@[stacks 01W8] #check
  (AlgebraicGeometry.projective_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Projective f ↔
        ∃ (P : AlgebraicGeometry.Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
          ℰ.IsFiniteType ∧ ℰ.IsQuasicoherent ∧
            ∃ _ : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation π ℰ,
              ∃ i : X ⟶ P, AlgebraicGeometry.ProjectivePresentation f π i)

/- Definition 29.43.1 (2): a scheme morphism is H-projective exactly when it admits a
closed-immersion presentation in a relative projective space of finite dimension. -/
@[stacks 01W8] #check
  (AlgebraicGeometry.hProjective_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.HProjective f ↔
        ∃ (n : ℕ) (P : AlgebraicGeometry.ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
          AlgebraicGeometry.ProjectivePresentation f P.hom i)

/- Definition 29.43.1 (3): a scheme morphism is locally projective exactly when its restriction
over every member of some open cover of the target is projective. -/
@[stacks 01W8] #check
  (AlgebraicGeometry.locallyProjective_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyProjective f ↔
        ∃ 𝒰 : AlgebraicGeometry.Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
          AlgebraicGeometry.Projective (f ∣_ ((𝒰.f i).opensRange)))
