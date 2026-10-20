/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FreeForgetResolution.AlternatingFace
import StacksCheckRecall

@[expose] public section

/-!
@stack 0G5T

# Example 14.34.4

Let `R` be a ring and `M` an `R`-module.  The source's simplicial module `X(M)` is the evaluated
canonical comonad resolution.  All construction data and the two derived comparison properties
are owned by `ModuleCat.FreeForgetResolution`; this file is intentionally only a chapter-facing
recall surface.
-/

open CategoryTheory
open CategoryTheory.ModuleCat.FreeForgetResolution
open Opposite
open scoped Simplicial IteratedEndofunctor

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.FreeForgetResolution

variable (R : Type u) [Ring R]
variable (M : ModuleCat R)
variable (n : ℕ) (x : M)

/- Example 14.34.4: the iterated free-forgetful resolution and its augmentation. -/
@[stacks 0G5T "Example 14.34.4 (canonical resolution)"]
#check (augmented R : SimplicialObject.Augmented (ModuleCat R ⥤ ModuleCat R))

@[stacks 0G5T "Example 14.34.4 (evaluation at M)"]
#check ((evaluation R).obj M : SimplicialObject.Augmented (ModuleCat R))

#check (evaluation R : ModuleCat R ⥤ SimplicialObject.Augmented (ModuleCat R))

#check (underlying.setFunctor_eq R :
  underlying.setFunctor R =
    evaluation R ⋙ SimplicialObject.Augmented.whiskeringObj
      (ModuleCat R) (Type u) (CategoryTheory.forget (ModuleCat R)))

#check (underlying.addCommGrpFunctor_comp_forget R :
  underlying.addCommGrpFunctor R ⋙ SimplicialObject.Augmented.whiskeringObj
      AddCommGrpCat (Type u) (CategoryTheory.forget AddCommGrpCat) =
    underlying.setFunctor R)

#check (complex R : ModuleCat R ⥤ ChainComplex (ModuleCat R) ℕ)
#check (augmentation R :
  complex R ⟶ evaluation R ⋙ SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ (ModuleCat R))

@[stacks 0G5T "Example 14.34.4 (degreewise shape)"]
#check (evaluation.obj_eq R M n :
  ((evaluation R).obj M).left.obj (op ⦋n⦌) = (comonad R).toFunctor ⁺⦋n⦌.obj M)

@[stacks 0G5T "Example 14.34.4 (iterated canonical generators)"]
#check (freeMk.iterate M n x : (functor R) ⁺⦋n⦌.obj M)

@[stacks 0G5T "Example 14.34.4 (inverse on canonical generators)"]
#check (underlying.set.inverse.app M n x :
  (underlying.set.inverse R M).app (op ⦋n⦌) x = freeMk.iterate M n x)

#check (underlying.set.zeroSection R M :
  (underlying.set R M).right ⟶ (underlying.set R M).left _⦋0⦌)

#check (underlying.set.inverse.app_zero R M :
  (underlying.set.inverse R M).app (op ⦋0⦌) = underlying.set.zeroSection R M)

#check (underlying.set.inverse.comp_hom R M :
  underlying.set.inverse R M ≫ (underlying.set R M).hom =
    𝟙 ((SimplicialObject.const (Type u)).obj (underlying.set R M).right))

#check (underlying.set.lastExtraDegeneracy R M :
  (underlying.set R M).LastExtraDegeneracy)

#check (underlying.set.homotopy R M :
  SimplicialObject.Homotopy (𝟙 (underlying.set R M).left)
    ((underlying.set R M).hom ≫ underlying.set.inverse R M))

@[stacks 0G5T "Example 14.34.4 (underlying-set homotopy equivalence)"]
#check (underlying.set.isHomotopyEquivalence R M :
  SimplicialObject.IsHomotopyEquivalence (underlying.set R M).hom)

#check (underlying.set.homotopyEquiv R M :
  SimplicialObject.HomotopyEquiv (underlying.set R M).left
    ((SimplicialObject.const (Type u)).obj (underlying.set R M).right))

#check (evaluation.hom_mem R M :
  SimplicialObject.ModuleCat.underlying.homotopyEquivalences R
    ((evaluation R).obj M).hom)

#check (augmentation.mem_quasiIso R :
  (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.down ℕ)).functorCategory
    (ModuleCat R) (augmentation R))

@[stacks 0G5T "Example 14.34.4 (alternating-face quasi-isomorphism)"]
#check (augmentation.quasiIso R M : QuasiIso ((augmentation R).app M))

end CategoryTheory.ModuleCat.FreeForgetResolution
