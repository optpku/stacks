/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

/-!
# Restriction of projective twist morphisms

Canonical twist multiplication and associated-module shift comparisons restrict to arbitrary
open subschemes through the strong-monoidal pullback functor on scheme modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.AssociatedModule

variable {A M : Type u} [CommRing A]
variable [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

namespace TwistMultiplication

/-- Restrict multiplication of two canonical twisting sheaves to an open subscheme of a
projective spectrum. -/
noncomputable def restrictOpenMap
    (T : TwistMultiplication 𝒜) (W : (Proj 𝒜).Opens) (a b : ℤ) :
    (tensorObj
      ((Scheme.Modules.pullback W.ι).obj (twistingSheaf 𝒜 a))
      ((Scheme.Modules.pullback W.ι).obj (twistingSheaf 𝒜 b)) :
      W.toScheme.Modules) ⟶
      (Scheme.Modules.pullback W.ι).obj (twistingSheaf 𝒜 (a + b)) :=
  Scheme.Modules.pullbackTensorMap W.ι (T.hom a b)

end TwistMultiplication

namespace ShiftComparison

/-- Restrict the canonical comparison from an associated module sheaf tensored with a twist to
the associated sheaf of the shifted grading to an open subscheme of a projective spectrum. -/
noncomputable def restrictOpenMap
    (C : ShiftComparison 𝒜 ℳ) (W : (Proj 𝒜).Opens) (k : ℤ) :
    (tensorObj
      ((Scheme.Modules.pullback W.ι).obj (sheaf 𝒜 ℳ))
      ((Scheme.Modules.pullback W.ι).obj (twistingSheaf 𝒜 k)) :
      W.toScheme.Modules) ⟶
      (Scheme.Modules.pullback W.ι).obj
        (sheaf 𝒜 (GradedModule.shiftGrading ℳ k)) :=
  Scheme.Modules.pullbackTensorMap W.ι (C.hom k)

end ShiftComparison

end AlgebraicGeometry.Proj.AssociatedModule
