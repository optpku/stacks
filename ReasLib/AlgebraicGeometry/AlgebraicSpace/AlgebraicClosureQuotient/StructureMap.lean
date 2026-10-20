/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability

/-!
# The structure morphism of the absolute Galois quotient

The structure map from the spectrum of the complex algebraic numbers to the
rational spectrum descends along the absolute Galois quotient sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- The structure morphism of the covering spectrum to the terminal rational scheme. -/
def coverToBase : cover ⟶ Over.mk (𝟙 base) :=
  Over.homMk cover.hom (by exact Category.comp_id _)

/-- The covering structure morphism is induced by the cover's underlying structure map. -/
theorem coverToBase_eq :
    coverToBase = Over.homMk cover.hom (by exact Category.comp_id _) := rfl

/-- The absolute Galois pre-relation equalizes the covering structure morphism. -/
theorem coverToBase_equalizes :
    (ofAut action).t ≫ coverToBase = (ofAut action).s ≫ coverToBase := by
  apply Over.OverMorphism.ext
  change (ofAut action).t.left ≫ cover.hom = (ofAut action).s.left ≫ cover.hom
  exact (Over.w (ofAut action).t).trans (Over.w (ofAut action).s).symm

/-- The structure morphism from the absolute Galois quotient to the rational spectrum. -/
def toSpec :
    sheafOfPoints ⟶
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj (Over.mk (𝟙 base)) :=
  (ofAut action).quotientSheafDesc (Scheme.fppfTopology.over base) coverToBase
    coverToBase_equalizes

/-- The quotient structure morphism is the descent of the covering structure morphism. -/
theorem toSpec_eq :
    toSpec =
      (ofAut action).quotientSheafDesc (Scheme.fppfTopology.over base) coverToBase
        coverToBase_equalizes := rfl

/-- Restricting the quotient structure morphism to its atlas gives the covering structure map. -/
theorem toSpec_comp_atlas :
    atlas ≫ toSpec =
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase :=
  (ofAut action).quotientSheafDesc_quotientMap (Scheme.fppfTopology.over base)
    coverToBase coverToBase_equalizes

/-- The structure morphism of a rational field extension to the terminal rational scheme. -/
def specToBase (L : Type) [Field L] [Algebra ℚ L] :
    Over.mk (FieldExtension.specMap ℚ L) ⟶ Over.mk (𝟙 base) :=
  Over.homMk (FieldExtension.specMap ℚ L) (by exact Category.comp_id _)

/-- The field-spectrum structure morphism is induced by the rational algebra map. -/
theorem specToBase_eq (L : Type) [Field L] [Algebra ℚ L] :
    specToBase L =
      Over.homMk (FieldExtension.specMap ℚ L) (by exact Category.comp_id _) := rfl

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
