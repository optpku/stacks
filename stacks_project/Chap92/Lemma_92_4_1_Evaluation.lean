module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Over
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver

/-!
# Cosimplicial evaluation on polynomial augmentations

This leaf converts a simplicial polynomial `A`-algebra with augmentation to `B` into a
cosimplicial object of `PolynomialSite A B`, and records the underlying simplicial-set
trivial Kan fibration hypothesis used to obtain pointlike mapping spaces.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open Algebra
open SSet.modelCategoryQuillen

universe u

namespace Algebra.PolynomialSite

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
variable (hP : ∀ n, IsPolynomial A (P.obj n))

/-- The underlying simplicial-set map of an augmentation of simplicial `A`-algebras. -/
def underlyingSSetMap :
    P ⋙ forget (CommAlgCat.{u} A) ⟶
      (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B) ⋙ forget (CommAlgCat.{u} A) :=
  Functor.whiskerRight ε (forget (CommAlgCat.{u} A))

/-- Components of `underlyingSSetMap` are the underlying maps of the algebra augmentation. -/
theorem underlyingSSetMap_app (n : SimplexCategoryᵒᵖ) :
    (underlyingSSetMap ε).app n = (forget (CommAlgCat.{u} A)).map (ε.app n) :=
  sorry

/-- The simplicial object of `PolynomialOver A B` associated to a simplicial polynomial
`A`-algebra with augmentation to `B`. -/
def asPolynomialSimplicial : SimplicialObject (PolynomialOver A B) :=
  (isPolynomialOver A B).lift (Augmented.toOver (Augmentation.toAugmented ε)) hP

/-- Degreewise, `asPolynomialSimplicial` is the over-object given by the augmentation
component. -/
theorem asPolynomialSimplicial_obj (n : SimplexCategoryᵒᵖ) :
    ((asPolynomialSimplicial ε hP).obj n).obj = Over.mk (ε.app n) :=
  sorry

/-- The cosimplicial object of `PolynomialSite A B` associated to a simplicial polynomial
augmentation. -/
noncomputable def asCosimplicial : CosimplicialObject (PolynomialSite A B) :=
  (asPolynomialSimplicial ε hP).rightOp

/-- Unpacking `asCosimplicial` in each degree recovers the corresponding augmentation
component. -/
theorem asCosimplicial_obj (n : SimplexCategory) :
    ((asCosimplicial ε hP).obj n).unop.obj = Over.mk (ε.app (Opposite.op n)) :=
  sorry

/-- A trivial Kan fibration on underlying simplicial sets makes `asCosimplicial` pointlike. -/
theorem asCosimplicial_hasHomSpaces (hε : I.rlp (underlyingSSetMap ε)) :
    CosimplicialObject.Pointlike.HasHomSpaces (asCosimplicial ε hP) :=
  sorry

end Algebra.PolynomialSite
