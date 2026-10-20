/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Stability
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings

@[expose] public section

open CategoryTheory
open scoped DerivedTensorChangeOfRings

noncomputable section

universe u

open scoped TensorProduct

namespace CategoryTheory.DerivedCategory.IsRelativeDualizingComplex

/-- The derived tensor product of relative dualizing complexes for two successive flat
finitely presented ring maps is relative dualizing for their composite. -/
theorem trans
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.Flat R A] [Module.Flat A B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B]
    [InternalHom.RHom.Has (A := A ⊗[R] A)]
    [InternalHom.RHom.Has (A := B ⊗[A] B)]
    [InternalHom.RHom.Has (A := B ⊗[R] B)]
    {KAR : DerivedCategory (ModuleCat A)} {KBA : DerivedCategory (ModuleCat B)}
    (hKAR : IsRelativeDualizingComplex R KAR)
    (hKBA : IsRelativeDualizingComplex A KBA) :
    @IsRelativeDualizingComplex R _ B _ _ (Module.Flat.trans R A B)
      (Algebra.FinitePresentation.trans R A B) inferInstance (KAR ⊗[A]^L[B] KBA) := sorry

end CategoryTheory.DerivedCategory.IsRelativeDualizingComplex
