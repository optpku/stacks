/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_4_1_Evaluation
public import stacks_project.Chap92.Lemma_92_4_2_Resolution
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Polynomial simplicial resolutions

A resolution of `B` over `A` is a simplicial polynomial `A`-algebra augmentation whose
underlying simplicial-set map is a trivial Kan fibration.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open Algebra
open SSet.modelCategoryQuillen

universe u

namespace Algebra.PolynomialSite

variable {A : Type u} [CommRing A]

/-- The forgetful functor from commutative `A`-algebras to abelian groups. -/
def forgetToAddCommGrp : CommAlgCat.{u} A ⥤ AddCommGrpCat.{u} :=
  forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙
    forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u}

/-- Unfolding `forgetToAddCommGrp` recovers the three-step ring forgetful composite. -/
theorem forgetToAddCommGrp_eq :
    forgetToAddCommGrp =
      forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙
        forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u} :=
  sorry

/-- The underlying simplicial abelian group of a simplicial commutative `A`-algebra. -/
def underlyingAddCommGrp (P : SimplicialObject (CommAlgCat.{u} A)) :
    SimplicialObject AddCommGrpCat.{u} :=
  P ⋙ forgetToAddCommGrp

/-- Degreewise, `underlyingAddCommGrp` applies `forgetToAddCommGrp`. -/
theorem underlyingAddCommGrp_obj (P : SimplicialObject (CommAlgCat.{u} A))
    (n : SimplexCategoryᵒᵖ) :
    (underlyingAddCommGrp P).obj n = forgetToAddCommGrp.obj (P.obj n) :=
  sorry

variable {B : Type u} [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))

/-- The underlying map of simplicial abelian groups of an algebra augmentation. -/
def underlyingAddCommGrpMap :
    underlyingAddCommGrp P ⟶
      underlyingAddCommGrp ((const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)) :=
  Functor.whiskerRight ε forgetToAddCommGrp

/-- Components of `underlyingAddCommGrpMap` are the underlying abelian-group maps of the
algebra augmentation. -/
theorem underlyingAddCommGrpMap_app (n : SimplexCategoryᵒᵖ) :
    (underlyingAddCommGrpMap ε).app n = forgetToAddCommGrp.map (ε.app n) :=
  sorry

/-- An augmentation of a simplicial `A`-algebra is a resolution of `B` over `A` when each
term is a polynomial `A`-algebra and the underlying simplicial-set map is a trivial Kan
fibration. -/
class IsResolution
    (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)) : Prop where
  /-- Each term of the simplicial algebra is a polynomial `A`-algebra. -/
  isPolynomial : ∀ n, IsPolynomial A (P.obj n)
  /-- The underlying simplicial-set map is a trivial Kan fibration. -/
  trivialKan : I.rlp (underlyingSSetMap ε)

namespace IsResolution

/-- Being a resolution is equivalent to the degreewise polynomial condition together with the
trivial Kan fibration condition on the underlying simplicial-set map. -/
theorem iff :
    IsResolution ε ↔
      (∀ n, IsPolynomial A (P.obj n)) ∧ I.rlp (underlyingSSetMap ε) :=
  sorry

/-- A resolution is degreewise polynomial and a trivial Kan fibration on underlying
simplicial sets. -/
theorem spec [IsResolution ε] :
    (∀ n, IsPolynomial A (P.obj n)) ∧ I.rlp (underlyingSSetMap ε) :=
  sorry

/-- A degreewise polynomial augmentation whose underlying simplicial-set map is a trivial Kan
fibration is a resolution. -/
theorem of_rlp (hP : ∀ n, IsPolynomial A (P.obj n))
    (hε : I.rlp (underlyingSSetMap ε)) : IsResolution ε :=
  sorry

/-- The cosimplicial object of `PolynomialSite A B` associated to a resolution. -/
noncomputable def asCosimplicial [IsResolution ε] :
    CosimplicialObject (PolynomialSite A B) :=
  Algebra.PolynomialSite.asCosimplicial ε (isPolynomial ε)

/-- Unfolding `IsResolution.asCosimplicial` recovers `asCosimplicial` of the polynomial
field. -/
theorem asCosimplicial_eq [IsResolution ε] :
    asCosimplicial ε = Algebra.PolynomialSite.asCosimplicial ε (isPolynomial ε) :=
  sorry

end IsResolution

variable (A B) in
/-- The standard polynomial resolution of `B` over `A` is a resolution. -/
instance instIsResolution_standardHom : IsResolution (standardHom A B) where
  isPolynomial := standard_isPolynomial A B
  trivialKan := standardHom_rlp A B

end Algebra.PolynomialSite

