/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.AlternatingFace
import StacksCheckRecall

@[expose] public section

/-!
@stack 08NA

# Example 14.34.5

The polynomial `A`-algebra resolution is the evaluated comonad resolution on `Under A`.  Its
canonical owner and its set/module views live in `CommRingCat.Under.PolynomialResolution`; this
file is a source-facing recall block.
-/

open CategoryTheory
open CategoryTheory.CommRingCat.Under.PolynomialResolution
open Under

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

variable (A : CommRingCat.{u})
variable (B : Under A)

/- Example 14.34.5: the augmented polynomial resolution and its evaluated views. -/
@[stacks 08NA "Example 14.34.5 (canonical resolution)"]
#check (augmented A : SimplicialObject.Augmented (Under A ⥤ Under A))

@[stacks 08NA "Example 14.34.5 (evaluation at B)"]
#check ((evaluation A).obj B : SimplicialObject.Augmented (Under A))

#check (evaluation A : Under A ⥤ SimplicialObject.Augmented (Under A))

#check (underlying.setFunctor_eq A :
  underlying.setFunctor A =
    evaluation A ⋙ SimplicialObject.Augmented.whiskeringObj
      (Under A) (Type u) (CommRingCat.Under.FreeAlgebra.carrier A))

#check (underlying.moduleFunctor_comp_forget A :
  underlying.moduleFunctor A ⋙ SimplicialObject.Augmented.whiskeringObj
      (ModuleCat A) (Type u) (CategoryTheory.forget (ModuleCat A)) =
    underlying.setFunctor A)

#check (complex A : Under A ⥤ ChainComplex (ModuleCat A) ℕ)
#check (augmentation A :
  complex A ⟶ underlying.moduleFunctor A ⋙ SimplicialObject.Augmented.point ⋙
    ChainComplex.single₀ (ModuleCat A))

@[stacks 08NA "Example 14.34.5 (underlying sets)"]
#check (underlying.set A B : SimplicialObject.Augmented (Type u))

@[stacks 08NA "Example 14.34.5 (underlying modules)"]
#check (underlying.module A B : SimplicialObject.Augmented (ModuleCat A))

@[stacks 08NA "Example 14.34.5 (underlying-set homotopy equivalence)"]
#check (underlying.set.isHomotopyEquivalence A B :
  SimplicialObject.IsHomotopyEquivalence (underlying.set A B).hom)

#check (underlying.set.homotopyEquiv A B :
  SimplicialObject.HomotopyEquiv (underlying.set A B).left
    ((SimplicialObject.const (Type u)).obj (underlying.set A B).right))

#check (underlying.set.lastExtraDegeneracy A B :
  (underlying.set A B).LastExtraDegeneracy)

#check (underlying.set.homotopy A B :
  SimplicialObject.Homotopy (𝟙 (underlying.set A B).left)
    ((underlying.set A B).hom ≫ underlying.set.inverse A B))

#check (underlying.module.hom_mem A B :
  SimplicialObject.ModuleCat.underlying.homotopyEquivalences A
    (underlying.module A B).hom)

#check (augmentation.mem_quasiIso A :
  (HomologicalComplex.quasiIso (ModuleCat A) (ComplexShape.down ℕ)).functorCategory
    (Under A) (augmentation A))

@[stacks 08NA "Example 14.34.5 (alternating-face quasi-isomorphism)"]
#check (augmentation.quasiIso A B : QuasiIso ((augmentation A).app B))

end CategoryTheory.CommRingCat.Under.PolynomialResolution
