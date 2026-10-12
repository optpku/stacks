/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability
public import stacks_project.Chap65.Example_65_14_7_Space

/-!
# The structure morphism of `Spec algebraicQ / Gal(algebraicQ / ℚ)`

This module records the structure morphism of the fppf quotient sheaf
`X = [Spec algebraicQ / Gal(algebraicQ / ℚ)]` over `S = Spec ℚ`, obtained by
descending the cover `Spec algebraicQ ⟶ Spec ℚ` along the Galois pre-relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- The structure morphism of `U = Spec algebraicQ` over `S = Spec ℚ`, as a
morphism to the terminal object `Over.mk (𝟙 base)` of `Over base`. -/
theorem coverToBase_w : cover.hom ≫ (Over.mk (𝟙 base)).hom = cover.hom := sorry

/-- The structure morphism of the atlas `U = Spec algebraicQ` over `S = Spec ℚ`. -/
def coverToBase : cover ⟶ Over.mk (𝟙 base) :=
  Over.homMk cover.hom coverToBase_w

/-- `coverToBase` is `Over.homMk` of the structure morphism of `cover`. -/
theorem coverToBase_eq : coverToBase = Over.homMk cover.hom coverToBase_w := sorry

/-- The Galois pre-relation equalizes `coverToBase`, since the action lies over
`Spec ℚ`. -/
theorem coverToBase_equalizes :
    (ofAut action).t ≫ coverToBase = (ofAut action).s ≫ coverToBase := sorry

/-- The structure morphism
`X = [Spec algebraicQ / Gal(algebraicQ / ℚ)] ⟶ S = Spec ℚ` of Spaces,
obtained by descending `coverToBase` along the Galois quotient sheaf. -/
def toSpec :
    sheafOfPoints ⟶
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj (Over.mk (𝟙 base)) :=
  (ofAut action).quotientSheafDesc (Scheme.fppfTopology.over base) coverToBase
    coverToBase_equalizes

/-- `toSpec` is the quotient-sheaf descent of `coverToBase`. -/
theorem toSpec_eq :
    toSpec =
      (ofAut action).quotientSheafDesc (Scheme.fppfTopology.over base) coverToBase
        coverToBase_equalizes := sorry

/-- On the atlas, `toSpec` recovers the structure morphism of `Spec algebraicQ`. -/
theorem toSpec_comp_atlas :
    atlas ≫ toSpec =
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase := sorry

/-- The triangle witnessing that `Spec L ⟶ Spec ℚ` is a morphism over `Spec ℚ`. -/
theorem specToBase_w (L : Type) [Field L] [Algebra ℚ L] :
    FieldExtension.specMap ℚ L ≫ (Over.mk (𝟙 base)).hom =
      (Over.mk (FieldExtension.specMap ℚ L)).hom := sorry

/-- The structure morphism of `Spec L` over `Spec ℚ`, as a morphism to the
terminal object `Over.mk (𝟙 base)`. -/
def specToBase (L : Type) [Field L] [Algebra ℚ L] :
    Over.mk (FieldExtension.specMap ℚ L) ⟶ Over.mk (𝟙 base) :=
  Over.homMk (FieldExtension.specMap ℚ L) (specToBase_w L)

/-- `specToBase L` is `Over.homMk` of `FieldExtension.specMap ℚ L`. -/
theorem specToBase_eq (L : Type) [Field L] [Algebra ℚ L] :
    specToBase L = Over.homMk (FieldExtension.specMap ℚ L) (specToBase_w L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
