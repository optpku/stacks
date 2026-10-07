module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap76.Lemma_76_9_7_SquareZero
public import stacks_project.Chap91.Lemma_91_14_3_Extension

/-!
# Solutions of 91.13.0.1 for a first-order thickening of algebraic spaces

A solution of the displayed first-order deformation equation for a morphism
`f : X ⟶ B` and a first-order thickening `i : B ⟶ B'` is an identity-base
square-zero `f⁻¹𝒪_{B'}`-algebra extension of `𝒪_X` whose induced map on
kernels equals the given coefficient `c : f⁻¹J ⟶ ℱ` of `f⁻¹𝒪_B`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.ObjectProperty CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.ThickeningSolution

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- The inverse-image thickening map `π = f⁻¹(i^♯) : (f ≫ i)⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B`. -/
def inverseImageThickeningMap (i : B ⟶ B') (f : X ⟶ B) :
    commInverseImageStructureSheaf (f ≫ i) ⟶ commInverseImageStructureSheaf f :=
  (commSheafInverseImageCompIso f i (commStructureSheaf B')).inv ≫
    commSheafInverseImageMap f (commInverseImageStructureSheafMap i)

/-- The inverse-image thickening map fits in the triangle with `f^♯` and `(f ≫ i)^♯`. -/
theorem inverseImageThickeningMap_comp (i : B ⟶ B') (f : X ⟶ B) :
    inverseImageThickeningMap i f ≫ commInverseImageStructureSheafMap f =
      commInverseImageStructureSheafMap (f ≫ i) :=
  sorry

/-- Inverse image of a first-order thickening remains locally surjective. -/
instance instIsLocallySurjective_inverseImageThickeningMap
    (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) :
    Sheaf.IsLocallySurjective (inverseImageThickeningMap i f) :=
  sorry

/-- Inverse image of a first-order thickening remains square zero. -/
theorem isSquareZero_inverseImageThickeningMap
    (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) :
    KernelIdeal.IsSquareZero (inverseImageThickeningMap i f) :=
  sorry

/-- The inverse image `f⁻¹J` of the thickening ideal, as an `f⁻¹𝒪_B`-module. -/
def inverseImageIdeal (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) :
    ringedSiteModuleCategory.{u + 1, u, u, u}
      (smallEtaleTopology X) (commInverseImageStructureSheaf f) :=
  @KernelIdeal.IsSquareZero.targetModule.{u + 1, u, u}
    (smallEtaleSite X) _ (smallEtaleTopology X) _
    (commInverseImageStructureSheaf (f ≫ i)) (commInverseImageStructureSheaf f)
    (inverseImageThickeningMap i f) _ _ _ _
    (isSquareZero_inverseImageThickeningMap i f)
    (KernelIdeal.quotientComparison_isIso (inverseImageThickeningMap i f))

/-- Maps of `f⁻¹𝒪_B`-modules from `f⁻¹J` to an `𝒪_X`-module `ℱ`. -/
abbrev Coeff (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) (ℱ : X.Modules) :=
  inverseImageIdeal i f ⟶
    (restrictionAlong.{u + 1, u, u, u} (commInverseImageStructureSheafMap f)).obj
      ((toCommModules X).obj ℱ)

/-- The composite of the kernel inclusion of `π` with the additive map of a commuting
structure map is killed by the projection of the unknown thickening. -/
theorem inducedAdditiveMap_lift_zero (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B)
    {ℱ : X.Modules} (E : SquareZeroAlgebraExtension (f ≫ i) ℱ) :
    ((SheafOfModules.toSheaf
          (ringSheaf.{u + 1, u, u} (smallEtaleTopology X)
            (commInverseImageStructureSheaf (f ≫ i)))).map
        (KernelIdeal.ι (inverseImageThickeningMap i f)) ≫
      SheafOfModules.unitUnderlyingMap (ringSheafMap.{u + 1, u, u} E.structureMap)) ≫
      (SheafOfModules.toSheaf
          (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) E.middle)).map
        (KernelIdeal.map E.proj) = 0 :=
  sorry

/-- The additive sheaf map of kernels induced by a commuting structure map. -/
def inducedAdditiveMap (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B)
    {ℱ : X.Modules} (E : SquareZeroAlgebraExtension (f ≫ i) ℱ) :
    (SheafOfModules.toSheaf
        (ringSheaf.{u + 1, u, u} (smallEtaleTopology X)
          (commInverseImageStructureSheaf f))).obj
      (inverseImageIdeal i f) ⟶
      (SheafOfModules.toSheaf
        (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X))).obj
      (E.proj_squareZero.targetModule E.proj_quotient_isIso) :=
  (@KernelIdeal.IsSquareZero.targetModuleForgetIso.{u + 1, u, u}
      (smallEtaleSite X) _ (smallEtaleTopology X) _
      (commInverseImageStructureSheaf (f ≫ i)) (commInverseImageStructureSheaf f)
      (inverseImageThickeningMap i f) _ _ _ _
      (isSquareZero_inverseImageThickeningMap i f)
      (KernelIdeal.quotientComparison_isIso (inverseImageThickeningMap i f))).hom ≫
    KernelIdeal.additiveLift E.proj
      ((SheafOfModules.toSheaf
          (ringSheaf.{u + 1, u, u} (smallEtaleTopology X)
            (commInverseImageStructureSheaf (f ≫ i)))).map
        (KernelIdeal.ι (inverseImageThickeningMap i f)) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap.{u + 1, u, u} E.structureMap))
      (inducedAdditiveMap_lift_zero i f E) ≫
    (E.proj_squareZero.targetModuleForgetIso E.proj_quotient_isIso).inv

/-- The coefficient `c_𝒪'` induced by an identity-base square-zero `f⁻¹𝒪_{B'}`-algebra
extension of `𝒪_X`. -/
def inducedCoeff (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) {ℱ : X.Modules}
    (E : SquareZeroAlgebraExtension (f ≫ i) ℱ) : Coeff i f ℱ where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u}).map
        (inducedAdditiveMap i f E ≫
          (SheafOfModules.toSheaf
              (ringSheaf.{u + 1, u, u} (smallEtaleTopology X)
                (commStructureSheaf X))).map
            E.kernelIso.hom))
      (fun _ _ _ ↦ sorry)

/-- The underlying additive map of `inducedCoeff` is `inducedAdditiveMap` followed by
`kernelIso`. -/
theorem inducedCoeff_spec (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B)
    {ℱ : X.Modules} (E : SquareZeroAlgebraExtension (f ≫ i) ℱ) :
    (sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf
            (ringSheaf.{u + 1, u, u} (smallEtaleTopology X)
              (commInverseImageStructureSheaf f))).map
          (inducedCoeff i f E)) =
      (sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u}).map
        (inducedAdditiveMap i f E ≫
          (SheafOfModules.toSheaf
              (ringSheaf.{u + 1, u, u} (smallEtaleTopology X)
                (commStructureSheaf X))).map
            E.kernelIso.hom) :=
  sorry

/-- An identity-base square-zero `f⁻¹𝒪_{B'}`-algebra extension solves the deformation
equation for `c` when its induced kernel map equals `c`. -/
def isSolution (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) {ℱ : X.Modules}
    (c : Coeff i f ℱ) : ObjectProperty (SquareZeroAlgebraExtension (f ≫ i) ℱ) :=
  fun E ↦ inducedCoeff i f E = c

/-- Membership in the solution property is equality of the induced coefficient with `c`. -/
theorem isSolution_iff (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) {ℱ : X.Modules}
    (c : Coeff i f ℱ) (E : SquareZeroAlgebraExtension (f ≫ i) ℱ) :
    isSolution i f c E ↔ inducedCoeff i f E = c :=
  sorry

/-- The category of solutions of 91.13.0.1 for the pair `(ℱ, c)`. -/
abbrev Solution (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) {ℱ : X.Modules}
    (c : Coeff i f ℱ) :=
  (isSolution i f c).FullSubcategory

/-- The forgetful functor from solutions to identity-base square-zero `f⁻¹𝒪_{B'}`-algebra
extensions. -/
abbrev toExtension (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B) {ℱ : X.Modules}
    (c : Coeff i f ℱ) :
    Solution i f c ⥤ SquareZeroAlgebraExtension (f ≫ i) ℱ :=
  (isSolution i f c).ι

end AlgebraicGeometry.AlgebraicSpace.Hom.ThickeningSolution
