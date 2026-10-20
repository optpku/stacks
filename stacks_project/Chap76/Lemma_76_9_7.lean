/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.SquareZeroRealization
import StacksCheckRecall

/-!
# First-order thickenings from square-zero algebras on algebraic spaces

A locally surjective square-zero extension of `𝒪_X` on `X_étale` with quasi-coherent
kernel is realized by a first-order thickening over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension

universe u

/- Lemma 76.9.7: A locally surjective square-zero extension of the étale structure sheaf
with quasi-coherent kernel and a compatible base-algebra structure is realized by a
first-order thickening over the base, with an isomorphism compatible with both the
surjection and the base-algebra structure. -/
@[stacks 05ZT] #check
  (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.exists_firstOrderThickening :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      (f : X ⟶ B) (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
      (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
      (hπ : KernelIdeal.IsSquareZero π) [(kernelModule π hπ).IsQuasicoherent]
      (α : commInverseImageStructureSheaf f ⟶ A)
      (hα : α ≫ π = commInverseImageStructureSheafMap f),
      ∃ (X' : AlgebraicSpace S) (i : X ⟶ X') (s' : X' ⟶ B)
        (φ : commInverseImageStructureSheaf i ⟶ A),
        IsRealization f A π hπ α hα i s' φ)
