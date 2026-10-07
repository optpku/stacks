module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap76.Definition_76_21_1_NaiveCotangent
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Lemma_76_7_4

/-!
# Homology of naive cotangent complexes of morphisms of algebraic spaces

The cohomology sheaves of `NL[f]` are the objects `(NL[f]).homology i`. They are
quasi-coherent, vanish outside degrees `-1` and `0`, and the degree-zero homology is
canonically `Ω[f]` via the sheafified `Extension.toKaehler` augmentation.
-/

@[expose] public section

open Algebra Algebra.Extension Algebra.Generators
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex Opposite
open PresheafOfModules.DifferentialsConstruction
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The objectwise `Extension.toKaehler` map of the canonical self-presentation of `f`. -/
def toKaehler_app (f : X ⟶ Y) (U : (smallEtaleSite X)ᵒᵖ) :
    cotangentSpaceObj f U ⟶
      (relativeDifferentials' (commInverseImageStructureSheafMap f).hom).obj U :=
  -- Local instance justification (noncanonical choice): algebra `f⁻¹𝒪_Y(U) → 𝒪_X(U)`.
  letI := inverseImageAlgebra f U
  ModuleCat.ofHom (presentation f U).toExtension.toKaehler

/-- The presheaf morphism from the presentation cotangent space to relative differentials. -/
def toKaehlerPresheaf (f : X ⟶ Y) :
    cotangentSpacePresheaf f ⟶
      relativeDifferentials' (commInverseImageStructureSheafMap f).hom where
  app := toKaehler_app f
  naturality := sorry

/-- The sheafified map from the degree-zero term of `NL[f]` to `Ω[f]`. -/
def toKaehler (f : X ⟶ Y) : cotangentSpaceSheaf f ⟶ Ω[f] :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).map (toKaehlerPresheaf f)

/-- The outgoing differential of `NL[f]` into degree zero followed by `toKaehler` is zero. -/
theorem d_comp_toKaehler (f : X ⟶ Y) (i : ℤ) (hi : (up ℤ).Rel i 0) :
    (NL[f]).d i 0 ≫ toKaehler f = 0 :=
  sorry

/-- The canonical cochain comparison `NL[f] ⟶ Ω[f][0]`. -/
def augmentation (f : X ⟶ Y) :
    NL[f] ⟶ (single X.Modules (up ℤ) 0).obj Ω[f] :=
  mkHomToSingle (toKaehler f) (d_comp_toKaehler f)

/-- The degree-zero component of `augmentation` is `toKaehler` followed by the inverse of
`singleObjXSelf`. -/
theorem augmentation_f_zero (f : X ⟶ Y) :
    (augmentation f).f 0 = toKaehler f ≫ (singleObjXSelf (up ℤ) 0 (Ω[f])).inv :=
  sorry

/-- The canonical map `H^0(NL[f]) ⟶ Ω[f]` induced by `augmentation`. -/
def homologyZeroMap (f : X ⟶ Y) : (NL[f]).homology 0 ⟶ Ω[f] :=
  homologyMap (augmentation f) 0 ≫ (singleObjHomologySelfIso (up ℤ) 0 (Ω[f])).hom

/-- The outgoing differential of `NL[f]` in degree `0` is zero. -/
theorem degreeZero_sc_g (f : X ⟶ Y) : ((NL[f]).sc 0).g = 0 :=
  sorry

/-- The degree-zero short-complex differential of `NL[f]` followed by `toKaehler` is zero. -/
theorem sc_f_comp_toKaehler (f : X ⟶ Y) : ((NL[f]).sc 0).f ≫ toKaehler f = 0 :=
  sorry

/-- The short complex whose first map is the incoming differential of `NL[f]` at degree `0`
and whose second map is `toKaehler`. -/
def toKaehlerShortComplex (f : X ⟶ Y) : ShortComplex X.Modules :=
  ShortComplex.mk ((NL[f]).sc 0).f (toKaehler f) (sc_f_comp_toKaehler f)

/-- `toKaehler` is an epimorphism, as objectwise `Extension.toKaehler` is surjective. -/
instance toKaehler_epi (f : X ⟶ Y) : Epi (toKaehler f) :=
  sorry

/-- The short complex `d ⟶ toKaehler` is exact. -/
theorem toKaehlerShortComplex_exact (f : X ⟶ Y) : (toKaehlerShortComplex f).Exact :=
  sorry

/-- `toKaehler` is a cokernel of the incoming differential of `NL[f]` at degree `0`. -/
def toKaehlerIsCokernel (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ (toKaehler f) (toKaehlerShortComplex f).zero) :=
  @ShortComplex.Exact.gIsCokernel _ _ _ (toKaehlerShortComplex f) _
    (toKaehlerShortComplex_exact f) (toKaehler_epi f)

/-- Degree-zero homology data for `NL[f]`, presenting `Ω[f]` as the cokernel of the
incoming differential. -/
def degreeZeroHomologyData (f : X ⟶ Y) : ((NL[f]).sc 0).HomologyData :=
  ShortComplex.HomologyData.ofIsColimitCokernelCofork ((NL[f]).sc 0) (degreeZero_sc_g f)
    (CokernelCofork.ofπ (toKaehler f) (toKaehlerShortComplex f).zero)
    (toKaehlerIsCokernel f)

/-- The named inverse of `homologyZeroMap`, obtained from the cokernel presentation of
`toKaehler`. -/
def homologyZeroInv (f : X ⟶ Y) : Ω[f] ⟶ (NL[f]).homology 0 :=
  (degreeZeroHomologyData f).left.homologyIso.inv

/-- The degree-zero homology map followed by its named inverse is the identity. -/
theorem homologyZeroMap_comp_inv (f : X ⟶ Y) :
    homologyZeroMap f ≫ homologyZeroInv f = 𝟙 _ :=
  sorry

/-- The named degree-zero homology inverse followed by the forward map is the identity. -/
theorem homologyZeroInv_comp_map (f : X ⟶ Y) :
    homologyZeroInv f ≫ homologyZeroMap f = 𝟙 _ :=
  sorry

/-- Degree-zero homology of `NL[f]` is canonically the sheaf of relative differentials. -/
def homologyZeroIso (f : X ⟶ Y) : (NL[f]).homology 0 ≅ Ω[f] where
  hom := homologyZeroMap f
  inv := homologyZeroInv f
  hom_inv_id := homologyZeroMap_comp_inv f
  inv_hom_id := homologyZeroInv_comp_map f

/-- The forward morphism of `homologyZeroIso` is `homologyZeroMap`. -/
theorem homologyZeroIso_hom (f : X ⟶ Y) : (homologyZeroIso f).hom = homologyZeroMap f :=
  sorry

/-- The inverse morphism of `homologyZeroIso` is `homologyZeroInv`. -/
theorem homologyZeroIso_inv (f : X ⟶ Y) : (homologyZeroIso f).inv = homologyZeroInv f :=
  sorry

/-- The canonical map `H^0(NL[f]) ⟶ Ω[f]` is an isomorphism. -/
instance homologyZeroMap_isIso (f : X ⟶ Y) : IsIso (homologyZeroMap f) :=
  ⟨⟨homologyZeroInv f, homologyZeroMap_comp_inv f, homologyZeroInv_comp_map f⟩⟩

/-- Every homology sheaf of the naive cotangent complex of a morphism of algebraic spaces
is quasi-coherent. -/
instance homology_isQuasicoherent (f : X ⟶ Y) (i : ℤ) :
    ((NL[f]).homology i).IsQuasicoherent :=
  sorry

/-- The homology of the naive cotangent complex of a morphism of algebraic spaces vanishes
outside degrees `-1` and `0`. -/
theorem homology_isZero_of_ne_zero_or_negOne (f : X ⟶ Y) (i : ℤ)
    (hi_zero : i ≠ 0) (hi_negOne : i ≠ -1) :
    IsZero ((NL[f]).homology i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
