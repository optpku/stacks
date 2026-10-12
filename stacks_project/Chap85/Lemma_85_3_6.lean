/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import stacks_project.Chap85.Lemma_85_3_5

/-!
# Lemma 85.3.6

In Situation 85.3.3, restriction `F ↦ F_n` along `C_n ⥤ C_total` sends injective
objects of `Ab(C_total)` to injective objects of `Ab(C_n)`, and sends K-injective
cochain complexes in `Ab(C_total)` to K-injective complexes in `Ab(C_n)`.
-/

@[expose] public section

open CategoryTheory ComplexShape Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J] (n : SimplexCategory)
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- Lemma 85.3.6 (1): if `I` is injective in `Ab(C_total)`, then the restriction
`I_n` is injective in `Ab(C_n)`. -/
@[stacks 09WH, instance]
instance stageRestrict_preservesInjectiveObjects :
    (stageRestrict C J AddCommGrpCat.{w} n).PreservesInjectiveObjects :=
  sorry

/-- Restriction of an injective abelian sheaf on `C_total` along the degree-`n`
inclusion is injective on `C_n`. -/
theorem injective_stageRestrict (I : Sheaf (topology C J) AddCommGrpCat.{w})
    [Injective I] :
    Injective ((stageRestrict C J AddCommGrpCat.{w} n).obj I) :=
  sorry

/-- Lemma 85.3.6 (2): if `I` is a K-injective cochain complex in `Ab(C_total)`,
then the restricted complex `I_n` is K-injective in `Ab(C_n)`. -/
@[stacks 09WH, instance]
instance stageRestrict_isKInjective
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((stageRestrict C J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J] (n : SimplexCategory)
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (J (op n)).toGrothendieck AddCommGrpCat.{w}]

/-- Lemma 85.3.6 (3): in case B, if `I` is injective in `Ab(C_total)`, then the
restriction `I_n` is injective in `Ab(C_n)`. -/
@[stacks 09WH, instance]
instance fiberRestrict_preservesInjectiveObjects :
    (fiberRestrict F J AddCommGrpCat.{w} n).PreservesInjectiveObjects :=
  sorry

/-- Restriction of an injective abelian sheaf on `C_total` along the degree-`n`
fiber inclusion is injective on `C_n`. -/
theorem injective_fiberRestrict (I : Sheaf (topology F J) AddCommGrpCat.{w})
    [Injective I] :
    Injective ((fiberRestrict F J AddCommGrpCat.{w} n).obj I) :=
  sorry

/-- Lemma 85.3.6 (4): in case B, if `I` is a K-injective cochain complex in
`Ab(C_total)`, then the restricted complex `I_n` is K-injective in `Ab(C_n)`. -/
@[stacks 09WH, instance]
instance fiberRestrict_isKInjective
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((fiberRestrict F J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

end CategoryTheory.Grothendieck
