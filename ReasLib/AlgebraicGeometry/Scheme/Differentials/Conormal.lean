module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The conormal sequence for an immersion of schemes

For an immersion `i : Z ⟶ X` over a scheme `S`, the canonical conormal map and the
pullback comparison on relative differentials form a right-exact sequence

  `C_{Z/X} ⟶ i^* Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0`.

The two arrows and their short complex are explicit data. Exactness and epimorphy are recorded
separately.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal.Differentials

variable {Z X S : Scheme.{u}}

/-- The scalar extension to `O_Z` of the relative differentials of the
inverse-image structure-sheaf map associated to `X ⟶ S`. -/
noncomputable abbrev tensorTerm (i : Z ⟶ X) (f : X ⟶ S) : Z.Modules :=
  SheafOfModules.RingedSite.conormalTensorTerm
    (C := Opens Z) (J := Opens.grothendieckTopology Z)
    ((SheafOfModules.RingedSite.InverseImage.ringPullback
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
      (Opens.map i.base)).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom))
    (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)

/-- The canonical morphism from the scalar-extended inverse-image differential
term to the pullback of `Ω_{X/S}`. -/
noncomputable def pullbackInv (i : Z ⟶ X) (f : X ⟶ S) :
    AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.tensorTerm i f ⟶
      (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] :=
  (SheafOfModules.ChangeOfRings.extendScalars
      (SheafOfModules.RingedSite.InverseImage.Factorization.underlyingAdjointMap
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
        (Opens.map i.base)
        (RingedSpace.Hom.commRingSheafPushforwardMap i.toShHom))).map
    (SheafOfModules.RingedSite.RelativeDifferentials.comparisonInv
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
      (Opens.map i.base)
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom)) ≫
    (SheafOfModules.RingedSite.InverseImage.Factorization.pullbackIso
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
      (Opens.map i.base)
      (RingedSpace.Hom.commRingSheafPushforwardMap i.toShHom)).inv.app Ω[f.toShHom]

/-- Pulling back `Ω_{X/S}` along `i` is canonically the scalar extension to `O_Z` of the
relative differentials of the inverse-image ring-sheaf map. -/
noncomputable def pullbackIso (i : Z ⟶ X) (f : X ⟶ S) :
    (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] ≅
      AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.tensorTerm i f :=
  (SheafOfModules.RingedSite.InverseImage.Factorization.pullbackIso
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
      (Opens.map i.base)
      (RingedSpace.Hom.commRingSheafPushforwardMap i.toShHom)).app Ω[f.toShHom] ≪≫
    (SheafOfModules.ChangeOfRings.extendScalars
      (SheafOfModules.RingedSite.InverseImage.Factorization.underlyingAdjointMap
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
        (Opens.map i.base)
        (RingedSpace.Hom.commRingSheafPushforwardMap i.toShHom))).mapIso
      (SheafOfModules.RingedSite.RelativeDifferentials.comparisonIso
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
        (Opens.map i.base)
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom))

/-- The canonical conormal morphism `C_{Z/X} ⟶ i^* Ω_{X/S}` induced by the universal
derivation of `X` over `S`. -/
noncomputable def map (i : Z ⟶ X) (f : X ⟶ S) :
    Scheme.Hom.conormalSheaf i ⟶
      (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] :=
  conormalMap
      ((SheafOfModules.RingedSite.InverseImage.ringPullback
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
        (Opens.map i.base)).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom) ≫
    AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.pullbackInv i f

/-- Transporting the canonical conormal morphism through `pullbackIso` recovers the site-level
map induced by `x ↦ 1 ⊗ d x`. -/
theorem map_comp_pullbackIso (i : Z ⟶ X) (f : X ⟶ S) :
    map i f ≫ (pullbackIso i f).hom =
      conormalMap
        ((SheafOfModules.RingedSite.InverseImage.ringPullback
          (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Z)
          (Opens.map i.base)).map
            (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom))
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom) := sorry

/-- The canonical comparison `i^* Ω_{X/S} ⟶ Ω_{Z/S}` attached to the evident
commutative square over `S`. -/
noncomputable def comparison (i : Z ⟶ X) (f : X ⟶ S) :
    (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] ⟶
      Ω[(i ≫ f).toShHom] :=
  let sq : CommSq i (i ≫ f) f (𝟙 S) := ⟨by simp⟩
  RingedSpace.Hom.Differentials.comparison
    (sq.map (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace))

/-- The canonical right arrow in the conormal sequence is the pullback comparison on relative
differentials. -/
theorem comparison_isComparison (i : Z ⟶ X) (f : X ⟶ S) :
    RingedSpace.Hom.Differentials.IsComparison (comparison i f) :=
  let sq : CommSq i (i ≫ f) f (𝟙 S) := ⟨by simp⟩
  RingedSpace.Hom.Differentials.comparison_isComparison
    (sq.map (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace))

/-- The two canonical arrows in the conormal sequence have zero composite. -/
theorem map_comp_comparison (i : Z ⟶ X) (f : X ⟶ S) :
    map i f ≫ comparison i f = 0 := sorry

/-- The canonical conormal short complex associated to `i : Z ⟶ X` over `S`. -/
noncomputable def complex (i : Z ⟶ X) (f : X ⟶ S) : ShortComplex Z.Modules :=
  ShortComplex.mk (map i f) (comparison i f) (map_comp_comparison i f)

/-- The canonical conormal short complex of a scheme immersion is exact. -/
theorem exact (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) :
    (complex i f).Exact := sorry

/-- The comparison morphism at the right of the conormal sequence of an immersion is an
epimorphism. -/
instance comparison_epi (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) :
    Epi (comparison i f) := sorry

/-- For a scheme immersion, the canonical conormal complex is exact and its right arrow is an
epimorphism. -/
theorem exact_and_epi (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) :
    (complex i f).Exact ∧ Epi (comparison i f) :=
  ⟨exact i f, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom.Conormal.Differentials
