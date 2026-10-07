module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naive cotangent complexes of morphisms of ringed spaces

This module specializes the ringed-site naive cotangent complex to the inverse-image structure
sheaf morphism associated to a morphism of ringed spaces.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Sheaf
open CategoryTheory.Limits
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open TopCat.Sheaf
open scoped ZeroObject AlgebraicGeometry TensorProduct

noncomputable section

universe u
namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X Y : RingedSpace.{u}}

/-- The canonical `Under`-object on `X` determined by the
inverse-image structure-sheaf map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
abbrev inverseImageStructureSheafUnder (f : X ⟶ Y) :=
  Under.mk (inverseImageStructureSheafHomComm f)

/-- The naive cotangent complex of a morphism of ringed spaces
`f : X ⟶ Y`, defined as the opens-site specialization of the ringed-site construction applied to
the canonical inverse-image structure-sheaf morphism `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[stacks 08TN]
noncomputable abbrev naiveCotangent (f : X ⟶ Y) :
    CochainComplex (SheafOfModules X.ringCatSheaf) ℤ :=
  SheafOfModules.RingedSite.NaiveCotangent.obj _ (inverseImageStructureSheafUnder f)

/-- The opens-site notation for the naive cotangent complex of `f : X ⟶ Y`. -/
scoped[AlgebraicGeometry] notation:max "NL[" f "]" =>
  RingedSpace.naiveCotangent f

/-- The degree `-1` term of `NL[f]` is the conormal sheaf `I/I²` of the canonical presentation
of `𝒪_X` over `f⁻¹𝒪_Y`. -/
theorem naiveCotangent_X_negOne (f : X ⟶ Y) :
    (NL[f]).X (-1) =
      conormalSource
        (FreeAlgebra.Presentation.map _ (inverseImageStructureSheafUnder f)) := sorry

/-- The degree `0` term of `NL[f]` is its canonical base-changed relative-differentials term. -/
theorem naiveCotangent_X_zero (f : X ⟶ Y) :
    (NL[f]).X 0 =
      conormalTensorTerm
        (FreeAlgebra.Presentation.base _ (inverseImageStructureSheafUnder f))
        (FreeAlgebra.Presentation.map _ (inverseImageStructureSheafUnder f)) := sorry

/-- The differential `NL[f]^{-1} ⟶ NL[f]^0` is the conormal map of the canonical presentation. -/
theorem naiveCotangent_d_negOne_zero (f : X ⟶ Y) :
    (NL[f]).d (-1) 0 =
      conormalMap
        (FreeAlgebra.Presentation.base _ (inverseImageStructureSheafUnder f))
        (FreeAlgebra.Presentation.map _ (inverseImageStructureSheafUnder f)) := sorry

namespace NaiveCotangent

/-- The sheaf `Ω[X/Y]`, concentrated in degree zero, as the target of the canonical
augmentation of `NL[f]`. -/
@[stacks 08TN "degree-zero target"]
noncomputable abbrev differentialsComplex (f : X ⟶ Y) :
    CochainComplex X.Modules ℤ :=
  SheafOfModules.RingedSite.NaiveCotangent.differentialsComplex _
    (inverseImageStructureSheafUnder f)

/-- The canonical augmentation `NL[f] ⟶ Ω[X/Y][0]`. -/
@[stacks 08TN "canonical augmentation"]
noncomputable abbrev augmentation (f : X ⟶ Y) :
    RingedSpace.naiveCotangent f ⟶ differentialsComplex f :=
  SheafOfModules.RingedSite.NaiveCotangent.augmentation _
    (inverseImageStructureSheafUnder f)

namespace Augmentation

/-- The named inverse of the degree-zero homology map induced by the canonical augmentation. -/
@[stacks 08TN "augmentation homology inverse"]
noncomputable abbrev homologyMapZeroInv (f : X ⟶ Y) :
    (differentialsComplex f).homology 0 ⟶ (RingedSpace.naiveCotangent f).homology 0 :=
  SheafOfModules.RingedSite.NaiveCotangent.Augmentation.homologyMapZeroInv _
    (inverseImageStructureSheafUnder f)

/-- The literal degree-zero homology isomorphism induced by the canonical augmentation. -/
@[stacks 08TN "augmentation homology isomorphism"]
noncomputable abbrev homologyMapZeroIso (f : X ⟶ Y) :
    (RingedSpace.naiveCotangent f).homology 0 ≅ (differentialsComplex f).homology 0 :=
  SheafOfModules.RingedSite.NaiveCotangent.Augmentation.homologyMapZeroIso _
    (inverseImageStructureSheafUnder f)

/-- The augmentation homology map followed by its named inverse is the identity. -/
@[simp, stacks 08TN "augmentation homology forward-inverse law"]
theorem homologyMap_comp_zeroInv (f : X ⟶ Y) :
    HomologicalComplex.homologyMap (augmentation f) 0 ≫
      homologyMapZeroInv f = 𝟙 _ := sorry

/-- The named augmentation homology inverse followed by the map is the identity. -/
@[simp, stacks 08TN "augmentation homology inverse-forward law"]
theorem homologyMapZeroInv_comp (f : X ⟶ Y) :
    homologyMapZeroInv f ≫ HomologicalComplex.homologyMap (augmentation f) 0 = 𝟙 _ := sorry

end Augmentation

/-- The degree-zero component of the canonical augmentation is the conormal-sequence projection
to `Ω[X/Y]`. -/
theorem augmentation_f_zero (f : X ⟶ Y) :
    (augmentation f).f 0 =
      conormalToDifferentials
          (FreeAlgebra.Presentation.base _ (inverseImageStructureSheafUnder f))
          (FreeAlgebra.Presentation.map _ (inverseImageStructureSheafUnder f)) ≫
        (SheafOfModules.RingedSite.NaiveCotangent.differentialsIso _
          (inverseImageStructureSheafUnder f)).hom := sorry

/-- The degree-zero homology of `NL[f]` is canonically the sheaf `Ω[X/Y]` of relative
differentials. -/
@[stacks 08TN "degree-zero homology"]
noncomputable abbrev homologyZeroIso (f : X ⟶ Y) :
    (RingedSpace.naiveCotangent f).homology 0 ≅ RingedSpace.Hom.differentials f :=
  SheafOfModules.RingedSite.NaiveCotangent.homologyZeroIso _
    (inverseImageStructureSheafUnder f)

/-- The named inverse of the canonical augmentation map on degree-zero homology. -/
@[stacks 08TN "augmentation homology inverse"]
noncomputable abbrev homologyMapZeroInv (f : X ⟶ Y) :
    (RingedSpace.NaiveCotangent.differentialsComplex f).homology 0 ⟶
      (RingedSpace.naiveCotangent f).homology 0 :=
  SheafOfModules.RingedSite.NaiveCotangent.Augmentation.homologyMapZeroInv _
    (inverseImageStructureSheafUnder f)

/-- The literal degree-zero augmentation homology isomorphism for a ringed-space morphism. -/
@[stacks 08TN "augmentation homology isomorphism"]
noncomputable abbrev homologyMapZeroIso (f : X ⟶ Y) :
    (RingedSpace.naiveCotangent f).homology 0 ≅
      (RingedSpace.NaiveCotangent.differentialsComplex f).homology 0 :=
  SheafOfModules.RingedSite.NaiveCotangent.Augmentation.homologyMapZeroIso _
    (inverseImageStructureSheafUnder f)

/-- The canonical degree-zero homology map for a ringed-space morphism. -/
@[stacks 08TN "degree-zero homology map"]
noncomputable abbrev homologyZeroMap (f : X ⟶ Y) :
    (RingedSpace.naiveCotangent f).homology 0 ⟶ RingedSpace.Hom.differentials f :=
  SheafOfModules.RingedSite.NaiveCotangent.homologyZeroMap _
    (inverseImageStructureSheafUnder f)

/-- The named inverse of the canonical degree-zero homology map. -/
@[stacks 08TN "degree-zero homology inverse"]
noncomputable abbrev homologyZeroInv (f : X ⟶ Y) :
    RingedSpace.Hom.differentials f ⟶ (RingedSpace.naiveCotangent f).homology 0 :=
  SheafOfModules.RingedSite.NaiveCotangent.homologyZeroInv _
    (inverseImageStructureSheafUnder f)

/-- The canonical degree-zero homology map followed by its named inverse is the identity. -/
@[simp, stacks 08TN "degree-zero homology forward-inverse law"]
theorem homologyZeroMap_comp_inv (f : X ⟶ Y) :
    homologyZeroMap f ≫ homologyZeroInv f = 𝟙 _ := sorry

/-- The named degree-zero homology inverse followed by the forward map is the identity. -/
@[simp, stacks 08TN "degree-zero homology inverse-forward law"]
theorem homologyZeroInv_comp_map (f : X ⟶ Y) :
    homologyZeroInv f ≫ homologyZeroMap f = 𝟙 _ := sorry

/-- The forward projection of the ringed-space degree-zero homology isomorphism. -/
@[simp, stacks 08TN "degree-zero homology isomorphism hom"]
theorem homologyZeroIso_hom (f : X ⟶ Y) :
    (homologyZeroIso f).hom = homologyZeroMap f := sorry

/-- The inverse projection of the ringed-space degree-zero homology isomorphism. -/
@[simp, stacks 08TN "degree-zero homology isomorphism inverse"]
theorem homologyZeroIso_inv (f : X ⟶ Y) :
    (homologyZeroIso f).inv = homologyZeroInv f := sorry

end NaiveCotangent

end AlgebraicGeometry.RingedSpace

-- Both complexes and the augmentation are canonical specializations of the ringed-site owner;
-- their data are explicit, with `sorryAx` confined to inherited complex and isomorphism laws.
