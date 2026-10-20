module

public import ReasLib.CategoryTheory.Sites.Simplicial.Stage
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Injective abelian sheaves under stage restriction
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] (n : SimplexCategory)
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- Restriction to any stage of a simplicial diagram of morphisms of sites preserves
injective abelian sheaves. -/
instance stageRestrict_preservesInjectiveObjects :
    (stageRestrict C J AddCommGrpCat.{w} n).PreservesInjectiveObjects :=
  sorry

/-- Termwise restriction to any stage of a simplicial diagram of morphisms of sites
preserves K-injective cochain complexes of abelian sheaves. -/
instance stageRestrict_isKInjective
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((stageRestrict C J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

end CategoryTheory.SimplicialSites
