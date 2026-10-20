/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.AffineBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.ClosedImmersion

/-!
# Base change of adjoint module morphisms

Affine pushforward identifies vanishing of a module morphism and its adjoint after scheme
base change. For a closed immersion it also identifies epimorphisms.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
variable {ℱ : X.Modules} {ℋ : Z.Modules}
variable {B : AlgebraicSpace S} (f : X ⟶ B)
variable [ℱ.IsQuasicoherent] [ℋ.IsQuasicoherent]
variable (u : ℱ ⟶ (pushforward i).obj ℋ)

/-- For an affine morphism, a morphism into the pushforward of a quasi-coherent module
vanishes after any scheme base change if and only if its adjoint vanishes after that
base change. -/
@[stacks 0CW7]
theorem baseChangeMap_zero_iff_adjoint [Affine i] (T : SchemeOver B) :
    baseChangeMap f T.hom u = 0 ↔
      baseChangeMap (i ≫ f) T.hom (adjointToPushforward i u) = 0 :=
  sorry

/-- For a closed immersion, a morphism into the pushforward of a quasi-coherent module
is an epimorphism after any scheme base change if and only if its adjoint is an
epimorphism after that base change. -/
@[stacks 0CW7]
theorem baseChangeMap_epi_iff_adjoint [IsClosedImmersion i] (T : SchemeOver B) :
    Epi (baseChangeMap f T.hom u) ↔
      Epi (baseChangeMap (i ≫ f) T.hom (adjointToPushforward i u)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
