module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.Pushout
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Solution

/-!
# Pushout of thickening solutions along a coefficient map

Coefficient pushout sends a square-zero algebra extension with prescribed coefficient
`c` to an extension with coefficient the postcomposition of `c` along `φ : ℱ ⟶ 𝒢`.
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

/-- Coefficient pushout along `φ` restricted to the full subcategory of solutions. -/
def pushoutFunctor (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) :
    Solution i f c ⥤ Solution i f (coeffMap i f φ c) :=
  ObjectProperty.FullSubcategory.restrict
    (SquareZeroAlgebraExtension.pushoutFunctor (f ≫ i) φ) (pushout_mapsTo i f φ c)

/-- On underlying extensions, `pushoutFunctor` is identity-base pushout along φ. -/
theorem pushoutFunctor_obj (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) (S : Solution i f c) :
    ((pushoutFunctor i f φ c).obj S).obj =
      SquareZeroAlgebraExtension.pushout φ ((toExtension i f c).obj S) :=
  sorry

/-- Forgetting solutions after coefficient pushout is naturally isomorphic to pushing out
the underlying extensions. -/
def pushoutFunctor_comp_toExtension (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) :
    toExtension i f c ⋙ SquareZeroAlgebraExtension.pushoutFunctor (f ≫ i) φ ≅
      pushoutFunctor i f φ c ⋙ toExtension i f (coeffMap i f φ c) :=
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (SquareZeroAlgebraExtension.pushoutFunctor (f ≫ i) φ) (pushout_mapsTo i f φ c)).symm

/-- On a quasi-compact and quasi-separated algebraic space, coefficient pushout on
solutions with a prescribed induced coefficient is an equivalence whenever the derived
coherator image of the coefficient map is invertible. -/
instance pushout_isEquivalence (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) [IsIso (SquareZeroAlgebraExtension.dqMap φ)] :
    Functor.IsEquivalence (pushoutFunctor i f φ c) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.ThickeningSolution
