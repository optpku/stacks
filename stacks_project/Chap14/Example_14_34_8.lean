/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Contraction.UnderlyingSet
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Contraction.FreeResolution
import StacksCheckRecall

@[expose] public section

/-!
@stack 08NE

# Polynomial resolutions and their explicit contractions

This file is the source-facing facade for Example 14.34.8.  The reusable owner, its
underlying-set contraction, and the free-object contraction live in
`ReasLib.Algebra.Category.CommRingCat.PolynomialResolution`.
-/

open CategoryTheory
open Opposite
open scoped Simplicial

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

variable (A : CommRingCat.{u}) (B : Under A) (E : Type u)
variable (n : ℕ) (b : B.right) (e : E)

/- Example 14.34.8 (1): after forgetting to sets, the augmentation of the polynomial
resolution is a simplicial homotopy equivalence. -/
@[stacks 08NE "Example 14.34.8 (1)"]
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

/- Example 14.34.8 (2): its canonical unit-induced inverse is given degreewise by iterated
brackets and is a strict section of the augmentation. -/
@[stacks 08NE "Example 14.34.8 (2)"]
#check (underlying.set.inverse.app B n b :
  (underlying.set.inverse A B).app (op ⦋n⦌) b =
    CommRingCat.Under.FreeAlgebra.generator.iterate (A := A) B n b)

#check (underlying.set.inverse.app_zero A B :
  (underlying.set.inverse A B).app (op ⦋0⦌) = underlying.set.zeroSection A B)

#check (underlying.set.inverse.comp_hom A B :
  underlying.set.inverse A B ≫ (underlying.set A B).hom =
    𝟙 ((SimplicialObject.const (Type u)).obj (underlying.set A B).right))

/- Example 14.34.8 (3): on a free `A`-algebra, the augmentation is already a simplicial homotopy
equivalence before forgetting the algebra structure. -/
@[stacks 08NE "Example 14.34.8 (3)"]
#check (freeResolution.isHomotopyEquivalence A E :
  SimplicialObject.IsHomotopyEquivalence ((freeResolution A).obj E).hom)

#check (freeResolution_eq A :
  freeResolution A = CommRingCat.Under.FreeAlgebra.functor A ⋙ evaluation A)

#check (freeResolution.homotopyEquiv A E :
  SimplicialObject.HomotopyEquiv ((freeResolution A).obj E).left
    ((SimplicialObject.const (Under A)).obj ((freeResolution A).obj E).right))

#check (freeResolution.extraDegeneracy A E :
  ((freeResolution A).obj E).ExtraDegeneracy)

#check (freeResolution.homotopy A E :
  SimplicialObject.Homotopy
    (((freeResolution A).obj E).hom ≫ freeResolution.inverse A E)
      (𝟙 ((freeResolution A).obj E).left))

/- Example 14.34.8 (4): the structured inverse brackets every polynomial generator in each
simplicial degree and is a strict section of the augmentation. -/
@[stacks 08NE "Example 14.34.8 (4)"]
#check (freeResolution.inverse.app_generator A n e :
  ((freeResolution.inverse A E).app (op ⦋n⦌)).right
      (CommRingCat.Under.FreeAlgebra.generator A e) =
    CommRingCat.Under.FreeAlgebra.generator.iterate (A := A)
      ((freeResolution A).obj E).right n
      (CommRingCat.Under.FreeAlgebra.generator A e))

/- The categorical generator is the polynomial variable under the canonical free-algebra
comparison, so the same formula has the source's polynomial presentation. -/
#check (CommRingCat.Under.FreeAlgebra.toPolynomial_generator (A := A) (E := E) e)

#check (freeResolution.inverse.app_zero A E :
  (freeResolution.inverse A E).app (op ⦋0⦌) = freeResolution.zeroSection A E)

#check (freeResolution.inverse.comp_hom A E :
  freeResolution.inverse A E ≫ ((freeResolution A).obj E).hom =
    𝟙 ((SimplicialObject.const (Under A)).obj ((freeResolution A).obj E).right))

end CategoryTheory.CommRingCat.Under.PolynomialResolution
