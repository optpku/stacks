module

public import ReasLib.CategoryTheory.Sites.Grothendieck.LowerShriek
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Injective abelian sheaves under fiber restriction
-/

@[expose] public section

open CategoryTheory ComplexShape Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J] (n : SimplexCategory)
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (J (op n)).toGrothendieck AddCommGrpCat.{w}]

/-- Restriction to any component of a fiberwise simplicial site preserves injective
abelian sheaves. -/
instance fiberRestrict_preservesInjectiveObjects :
    (fiberRestrict F J AddCommGrpCat.{w} n).PreservesInjectiveObjects :=
  sorry

/-- Termwise restriction to any component of a fiberwise simplicial site preserves
K-injective cochain complexes of abelian sheaves. -/
instance fiberRestrict_isKInjective
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((fiberRestrict F J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

end CategoryTheory.Grothendieck
