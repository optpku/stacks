module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap76.Lemma_76_7_6_Comparison

/-!
# The conormal sequence of an immersion of algebraic spaces

For an immersion `i : Z ⟶ X` of algebraic spaces over `B`, the canonical
conormal map induced by `d_{X/B}` and the Lemma 76.7.6 comparison on relative
differentials form a right-exact sequence

  `C_{Z/X} ⟶ i^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0`.

`C_{Z/X}` is the coborder pullback of `I / I²` along `IsImmersion.liftCoborder i`.
The first arrow is induced on that closed immersion by `d_{U/B}`, then
transported to `i^* Ω_{X/B}` along the explicit étale-restriction inverse of
the open-immersion differentials comparison, `pullbackComp`, and `eqToIso` of
`liftCoborder_comp`. The second arrow is `Hom.Differentials.comparison` of the
identity square on `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open Sheaf.InternalModule
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials

variable {S : Scheme.{u}} {B X Z : AlgebraicSpace S}
variable (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ B)

/-- The `𝒪`-linear map `I ⟶ Ω_{U/B} / I Ω_{U/B}` induced by `d_{U/B}` on the
coborder closed immersion of `i`. -/
def toQuotientDifferentials :
    idealSheaf (IsImmersion.liftCoborder i) ⟶
      Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) :=
  homOfUnderlying (structureSheaf (IsImmersion.coborderRange i).X)
    (((ToInternal.underlying (structureSheaf (IsImmersion.coborderRange i).X)).map
        (idealSheafι (IsImmersion.liftCoborder i))) ≫
      (Modules.unitCarrierIso (IsImmersion.coborderRange i).X).hom ≫
      universalDerivation_typeHom ((IsImmersion.coborderRange i).ι ≫ f) ≫
      ((ToInternal.underlying (structureSheaf (IsImmersion.coborderRange i).X)).map
        (Modules.quotientByIdeal.π (idealSheafSubobject (IsImmersion.liftCoborder i))
          (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)))))
    sorry sorry

/-- The coborder derivation `I ⟶ Ω / IΩ` annihilates the ideal-sheaf action
`I ⊗ I ⟶ I`. -/
theorem toQuotientDifferentials_comp_action :
    Modules.idealAction (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i)) ≫
      toQuotientDifferentials i f =
      0 :=
  sorry

/-- The coborder quotient map `I / I² ⟶ Ω_{U/B} / I Ω_{U/B}` induced by
`d_{U/B}`. -/
def coborderQuotientMap :
    Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i)) ⟶
      Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) :=
  cokernel.desc
    (Modules.idealAction (idealSheafSubobject (IsImmersion.liftCoborder i))
      (idealSheaf (IsImmersion.liftCoborder i)))
    (toQuotientDifferentials i f) (toQuotientDifferentials_comp_action i f)

/-- `coborderQuotientMap` is cokernel descent of `toQuotientDifferentials`. -/
theorem coborderQuotientMap_eq :
    coborderQuotientMap i f =
      cokernel.desc
        (Modules.idealAction (idealSheafSubobject (IsImmersion.liftCoborder i))
          (idealSheaf (IsImmersion.liftCoborder i)))
        (toQuotientDifferentials i f) (toQuotientDifferentials_comp_action i f) :=
  sorry

/-- The adjoint `C_{Z/X} ⟶ j^* Ω_{U/B}` of the coborder quotient map composed
with `F / I F ⟶ j_* j^* F`. -/
def coborderMap :
    (Modules.pullback (IsImmersion.liftCoborder i)).obj
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i))) ⟶
      (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) :=
  ((Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).homEquiv
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i)))
      ((Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)))).symm
    (coborderQuotientMap i f ≫
      Modules.quotientByIdealComparison (IsImmersion.liftCoborder i)
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)))

/-- `coborderMap` is the adjunction transpose of
`coborderQuotientMap ≫ quotientByIdealComparison`. -/
theorem coborderMap_eq :
    coborderMap i f =
      ((Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).homEquiv
          (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
            (idealSheaf (IsImmersion.liftCoborder i)))
          ((Modules.pullback (IsImmersion.liftCoborder i)).obj
            (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)))).symm
        (coborderQuotientMap i f ≫
          Modules.quotientByIdealComparison (IsImmersion.liftCoborder i)
            (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f))) :=
  sorry

/-- The comparison `i^* Ω_{X/B} ⟶ j^* Ω_{U/B}` obtained from Lemma 76.7.6 along
the coborder open immersion, after `pullbackComp` and `liftCoborder_comp`. -/
def coborderDifferentialsComparison :
    (Modules.pullback i).obj (relativeDifferentials f) ⟶
      (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) :=
  (eqToIso (congrArg Modules.pullback (IsImmersion.liftCoborder_comp i))).inv.app
      (relativeDifferentials f) ≫
    (Modules.pullbackComp (IsImmersion.liftCoborder i)
        (IsImmersion.coborderRange i).ι).inv.app
      (relativeDifferentials f) ≫
    (Modules.pullback (IsImmersion.liftCoborder i)).map
      (Hom.Differentials.comparison
        (IsImmersion.coborderRange i).ι (𝟙 B) f
        ((IsImmersion.coborderRange i).ι ≫ f)
        (Eq.symm (Category.comp_id ((IsImmersion.coborderRange i).ι ≫ f))))

/-- The section map of the étale-restriction derivation sending a local section of
`𝒪_U` to `d_{X/B}` of the same section on the postcomposed étale object. -/
def coborderOpenRestrictSection
    {U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ}
    (t : (commStructureSheaf (IsImmersion.coborderRange i).X).obj.obj U) :
    (Modules.restrict (relativeDifferentials f)
        (IsImmersion.coborderRange i).ι).val.obj U :=
  (Modules.restrictAppIso (relativeDifferentials f)
      (IsImmersion.coborderRange i).ι U.unop).inv
    ((universalDerivation f).d (cast rfl t))

/-- Additivity of `coborderOpenRestrictSection`. -/
theorem coborderOpenRestrictSection_add
    {U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ}
    (a b : (commStructureSheaf (IsImmersion.coborderRange i).X).obj.obj U) :
    coborderOpenRestrictSection i f (a + b) =
      coborderOpenRestrictSection i f a + coborderOpenRestrictSection i f b :=
  sorry

/-- The Leibniz rule for `coborderOpenRestrictSection`. -/
theorem coborderOpenRestrictSection_mul
    {U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ}
    (a b : (commStructureSheaf (IsImmersion.coborderRange i).X).obj.obj U) :
    coborderOpenRestrictSection i f (a * b) =
      a • coborderOpenRestrictSection i f b +
        b • coborderOpenRestrictSection i f a :=
  sorry

/-- Naturality of `coborderOpenRestrictSection`. -/
theorem coborderOpenRestrictSection_naturality
    {U V : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ} (ρ : U ⟶ V)
    (t : (commStructureSheaf (IsImmersion.coborderRange i).X).obj.obj U) :
    coborderOpenRestrictSection i f
        ((commStructureSheaf (IsImmersion.coborderRange i).X).obj.map ρ t) =
      ((Modules.restrict (relativeDifferentials f)
          (IsImmersion.coborderRange i).ι).val.map ρ)
        (coborderOpenRestrictSection i f t) :=
  sorry

/-- `coborderOpenRestrictSection` vanishes on the inverse image of `𝒪_B`. -/
theorem coborderOpenRestrictSection_base {U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ}
    (a : (commInverseImageStructureSheaf ((IsImmersion.coborderRange i).ι ≫ f)).obj.obj U) :
    coborderOpenRestrictSection i f
      ((commInverseImageStructureSheafMap
          ((IsImmersion.coborderRange i).ι ≫ f)).hom.app U a) = 0 :=
  sorry

/-- The `B`-derivation of `U` into the étale restriction of `Ω_{X/B}` induced by
`d_{X/B}`. -/
def coborderOpenRestrictDerivation :
    (toCommPresheaf
        (Modules.restrict (relativeDifferentials f)
          (IsImmersion.coborderRange i).ι)).Derivation'
      (commInverseImageStructureSheafMap
        ((IsImmersion.coborderRange i).ι ≫ f)).hom where
  d {_} := AddMonoidHom.mk' (coborderOpenRestrictSection i f)
      (coborderOpenRestrictSection_add i f)
  d_mul := coborderOpenRestrictSection_mul i f
  d_map := coborderOpenRestrictSection_naturality i f
  d_app := coborderOpenRestrictSection_base i f

/-- Descent of `d_{X/B}` to an `𝒪_U`-linear map `Ω_{U/B} ⟶ Ω_{X/B}|_U`. -/
def coborderOpenRestrictDesc :
    relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f) ⟶
      Modules.restrict (relativeDifferentials f)
        (IsImmersion.coborderRange i).ι :=
  (PresheafOfModules.sheafificationHomEquiv.{u}
      (𝟙 (structureSheaf (IsImmersion.coborderRange i).X).obj)).symm
    ((isUniversal'
        (commInverseImageStructureSheafMap
          ((IsImmersion.coborderRange i).ι ≫ f)).hom).desc
      (cast rfl (coborderOpenRestrictDerivation i f)))

/-- The inverse `Ω_{U/B} ⟶ ι^* Ω_{X/B}` of the coborder open comparison, as descent
of `d_{X/B}` through étale restriction followed by `restrictIsoPullback`. -/
def coborderOpenComparisonInv :
    relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f) ⟶
      (Modules.pullback (IsImmersion.coborderRange i).ι).obj
        (relativeDifferentials f) :=
  coborderOpenRestrictDesc i f ≫
    (Modules.restrictIsoPullback (relativeDifferentials f)
        (IsImmersion.coborderRange i).ι).hom

/-- `coborderOpenComparisonInv` is `coborderOpenRestrictDesc` followed by
`restrictIsoPullback`. -/
theorem coborderOpenComparisonInv_eq :
    coborderOpenComparisonInv i f =
      coborderOpenRestrictDesc i f ≫
        (Modules.restrictIsoPullback (relativeDifferentials f)
            (IsImmersion.coborderRange i).ι).hom :=
  sorry

/-- The inverse transport `j^* Ω_{U/B} ⟶ i^* Ω_{X/B}` of the coborder open
comparison, as an explicit composite. -/
def coborderDifferentialsComparisonInv :
    (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) ⟶
      (Modules.pullback i).obj (relativeDifferentials f) :=
  (Modules.pullback (IsImmersion.liftCoborder i)).map
      (coborderOpenComparisonInv i f) ≫
    (Modules.pullbackComp (IsImmersion.liftCoborder i)
        (IsImmersion.coborderRange i).ι).hom.app
      (relativeDifferentials f) ≫
    (eqToIso (congrArg Modules.pullback (IsImmersion.liftCoborder_comp i))).hom.app
      (relativeDifferentials f)

/-- `coborderDifferentialsComparisonInv` is `j^*` of `coborderOpenComparisonInv`,
then `pullbackComp` and `eqToIso` of `liftCoborder_comp`. -/
theorem coborderDifferentialsComparisonInv_eq :
    coborderDifferentialsComparisonInv i f =
      (Modules.pullback (IsImmersion.liftCoborder i)).map
          (coborderOpenComparisonInv i f) ≫
        (Modules.pullbackComp (IsImmersion.liftCoborder i)
            (IsImmersion.coborderRange i).ι).hom.app
          (relativeDifferentials f) ≫
        (eqToIso (congrArg Modules.pullback (IsImmersion.liftCoborder_comp i))).hom.app
          (relativeDifferentials f) :=
  sorry

/-- The coborder open comparison on relative differentials as explicit isomorphism
data. -/
def coborderDifferentialsComparisonIso :
    (Modules.pullback i).obj (relativeDifferentials f) ≅
      (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) where
  hom := coborderDifferentialsComparison i f
  inv := coborderDifferentialsComparisonInv i f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The coborder open comparison on relative differentials is an isomorphism. -/
instance instIsIso_coborderDifferentialsComparison :
    IsIso (coborderDifferentialsComparison i f) :=
  (coborderDifferentialsComparisonIso i f).isIso_hom

/-- The canonical conormal morphism `C_{Z/X} ⟶ i^* Ω_{X/B}` induced by
`d_{X/B}`. -/
def map :
    (Modules.pullback (IsImmersion.liftCoborder i)).obj
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i))) ⟶
      (Modules.pullback i).obj (relativeDifferentials f) :=
  coborderMap i f ≫ coborderDifferentialsComparisonInv i f

/-- The canonical comparison `i^* Ω_{X/B} ⟶ Ω_{Z/B}` attached to the identity
square on `B`. -/
def comparison :
    (Modules.pullback i).obj (relativeDifferentials f) ⟶
      relativeDifferentials (i ≫ f) :=
  Hom.Differentials.comparison i (𝟙 B) f (i ≫ f)
    (Eq.symm (Category.comp_id (i ≫ f)))

/-- The two canonical arrows in the conormal sequence have zero composite. -/
theorem map_comp_comparison : map i f ≫ comparison i f = 0 :=
  sorry

/-- The canonical conormal short complex associated to an immersion over `B`. -/
def complex : ShortComplex Z.Modules :=
  ShortComplex.mk (map i f) (comparison i f) (map_comp_comparison i f)

/-- `complex` is the short complex on `map` and `comparison`. -/
theorem complex_eq :
    complex i f =
      ShortComplex.mk (map i f) (comparison i f) (map_comp_comparison i f) :=
  sorry

/-- The canonical conormal short complex of an immersion of algebraic spaces is
exact. -/
theorem exact : (complex i f).Exact :=
  sorry

/-- The comparison at the right of the conormal sequence of an immersion is an
epimorphism. -/
instance comparison_epi : Epi (comparison i f) :=
  sorry

/-- For an immersion of algebraic spaces over `B`, the canonical conormal complex
is exact and its right arrow is an epimorphism. -/
theorem exact_and_epi : (complex i f).Exact ∧ Epi (comparison i f) :=
  sorry

/-- The second arrow of the conormal sequence is the Lemma 76.7.6 comparison of
the identity square on `B`. -/
theorem comparison_isComparison :
    Hom.Differentials.IsComparison i f (i ≫ f) (comparison i f) :=
  sorry

/-- `map` is the coborder `d`-induced adjoint of `I / I² ⟶ j_* j^* Ω_{U/B}`,
transported to `i^* Ω_{X/B}` along the explicit coborder open comparison inverse. -/
theorem map_spec :
    map i f = coborderMap i f ≫ coborderDifferentialsComparisonInv i f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials
