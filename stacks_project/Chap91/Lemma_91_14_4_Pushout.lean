module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap91.Lemma_91_14_3_Pushout
public import stacks_project.Chap91.Lemma_91_14_4_Solution

/-!
# Pushout of thickening solutions along a coefficient map

The source functor FT sends a solution of 91.13.0.1 for (ℱ, c) to the pushout
along φ : ℱ ⟶ 𝒢, which is a solution for (𝒢, c') with c' the composite of c
and φ.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension
open AlgebraicGeometry.AlgebraicSpace.Hom.ThickeningSolution
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.ThickeningSolution

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}
variable (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules}

/-- The composite coefficient c' = c ≫ φ, as a map of f⁻¹𝒪_B-modules. -/
def coeffMap (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) : Coeff i f 𝒢 :=
  c ≫ (restrictionAlong (commInverseImageStructureSheafMap f)).map ((toCommModules X).map φ)

/-- `coeffMap φ c` is postcomposition of `c` with the restriction of `φ`. -/
theorem coeffMap_eq (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) :
    coeffMap i f φ c =
      c ≫ (restrictionAlong (commInverseImageStructureSheafMap f)).map ((toCommModules X).map φ) :=
  sorry

/-- Pushout along φ sends solutions for c to solutions for coeffMap φ c. -/
theorem pushout_mapsTo (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) :
    isSolution i f c ≤
      (isSolution i f (coeffMap i f φ c)).inverseImage
        (SquareZeroAlgebraExtension.pushoutFunctor (f ≫ i) φ) :=
  sorry

/-- The source functor FT, obtained by restricting identity-base pushout along φ
to the full subcategory of solutions. -/
def pushoutFunctor (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) :
    Solution i f c ⥤ Solution i f (coeffMap i f φ c) :=
  ObjectProperty.FullSubcategory.restrict
    (SquareZeroAlgebraExtension.pushoutFunctor (f ≫ i) φ) (pushout_mapsTo i f φ c)

/-- On underlying extensions, `pushoutFunctor` is identity-base pushout along φ. -/
theorem pushoutFunctor_obj (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) (S : Solution i f c) :
    ((pushoutFunctor i f φ c).obj S).obj =
      SquareZeroAlgebraExtension.pushout φ ((toExtension i f c).obj S) :=
  sorry

/-- Forgetting solutions after FT recovers identity-base pushout after forgetting. -/
def pushoutFunctor_comp_toExtension (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) :
    toExtension i f c ⋙ SquareZeroAlgebraExtension.pushoutFunctor (f ≫ i) φ ≅
      pushoutFunctor i f φ c ⋙ toExtension i f (coeffMap i f φ c) :=
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (SquareZeroAlgebraExtension.pushoutFunctor (f ≫ i) φ) (pushout_mapsTo i f φ c)).symm

end AlgebraicGeometry.AlgebraicSpace.Hom.ThickeningSolution
