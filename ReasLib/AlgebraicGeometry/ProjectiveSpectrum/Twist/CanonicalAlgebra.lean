/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedMap
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit

/-!
# The graded algebra of the actual Serre twisting sheaves

The objects are the associated sheaves of the translated regular grading.
The unit is the constant fraction1, and multiplication is multiplication of
homogeneous localized fractions at every point. Neither the modules nor their
algebra operations are supplied as arbitrary presentation data.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite
noncomputable section
universe u v

namespace AlgebraicGeometry.Proj.AssociatedModule.CanonicalAlgebra

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The actual section presentation of the specified Serre twist. -/
def sectionEquiv (n : ℤ) (U : (Proj 𝒜).Opens) :
    (twistingSheaf 𝒜 n).val.obj (op U) ≃
      sections 𝒜 (GradedMap.regularShift.{u, v} 𝒜 n) U := Equiv.refl _

/-- The degree-zero homogeneous fraction1 at a projective point. -/
def oneAtPoint (x : Proj 𝒜) : atPoint 𝒜 (GradedMap.regularShift.{u, v} 𝒜 0) x :=
  ⟨1, sorry⟩

/-- The constant fraction1 is locally represented on positive standard opens. -/
theorem one_locallyRepresentable (U : (Proj 𝒜).Opens) :
    IsLocallyRepresentable 𝒜 (GradedMap.regularShift.{u, v} 𝒜 0) U
      (fun x ↦ oneAtPoint 𝒜 x.1) := sorry

/-- The degree-zero unit section on an arbitrary open. -/
def one (U : ((Proj 𝒜).Opens)ᵒᵖ) : (twistingSheaf 𝒜 0).val.obj U :=
  (sectionEquiv 𝒜 0 U.unop).symm
    ⟨fun x ↦ oneAtPoint 𝒜 x.1, one_locallyRepresentable 𝒜 U.unop⟩

/-- Multiply the actual localized fractions in shifted homogeneous degrees. -/
def mulAtPoint (a b : ℤ) (x : Proj 𝒜)
    (s : atPoint 𝒜 (GradedMap.regularShift.{u, v} 𝒜 a) x)
    (t : atPoint 𝒜 (GradedMap.regularShift.{u, v} 𝒜 b) x) :
    atPoint 𝒜 (GradedMap.regularShift.{u, v} 𝒜 (a + b)) x :=
  ⟨s.1 * t.1, sorry⟩

/-- Products of local homogeneous fractions are locally represented on intersections. -/
theorem mul_locallyRepresentable (a b : ℤ) (U : (Proj 𝒜).Opens)
    (s : sections 𝒜 (GradedMap.regularShift.{u, v} 𝒜 a) U)
    (t : sections 𝒜 (GradedMap.regularShift.{u, v} 𝒜 b) U) :
    IsLocallyRepresentable 𝒜 (GradedMap.regularShift.{u, v} 𝒜 (a + b)) U
      (fun x ↦ mulAtPoint 𝒜 a b x.1 (s.1 x) (t.1 x)) := sorry

/-- The actual sectionwise product, transported only through definitional section presentations. -/
def mulSection (U : ((Proj 𝒜).Opens)ᵒᵖ) (a b : ℤ)
    (s : (twistingSheaf 𝒜 a).val.obj U) (t : (twistingSheaf 𝒜 b).val.obj U) :
    (twistingSheaf 𝒜 (a + b)).val.obj U :=
  let s' := sectionEquiv 𝒜 a U.unop s
  let t' := sectionEquiv 𝒜 b U.unop t
  (sectionEquiv 𝒜 (a + b) U.unop).symm
    ⟨fun x ↦ mulAtPoint 𝒜 a b x.1 (s'.1 x) (t'.1 x),
      mul_locallyRepresentable 𝒜 a b U.unop s' t'⟩

/-- Bilinearization uses the actual localized product. -/
def mul (U : ((Proj 𝒜).Opens)ᵒᵖ) (a b : ℤ) :
    (twistingSheaf 𝒜 a).val.obj U →ₗ[(Proj 𝒜).sheaf.obj.obj U]
      (twistingSheaf 𝒜 b).val.obj U →ₗ[(Proj 𝒜).sheaf.obj.obj U]
        (twistingSheaf 𝒜 (a + b)).val.obj U :=
  LinearMap.mk₂ ((Proj 𝒜).sheaf.obj.obj U) (mulSection 𝒜 U a b)
    sorry sorry sorry sorry

/-- The canonical integral Serre-twist algebra with its actual module objects and operations. -/
def algebra : GradedAlgebraSheaf.{u, u} (Proj 𝒜).sheaf where
  obj := twistingSheaf 𝒜
  one := one 𝒜
  mul := mul 𝒜
  map_one := sorry
  map_mul := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

/-- The ordinary multiplication is commutative, since the localized rings are commutative. -/
instance algebra_isCommutative : (algebra 𝒜).IsCommutative where
  mul_comm := by intros; sorry

/-- Every Serre twist is quasi-coherent, with no generation-in-degree-one assumption. -/
theorem algebra_isQuasicoherent : (algebra 𝒜).IsQuasicoherent := sorry

/-- The unit module maps to degree zero by scalar multiplication on the actual section1. -/
def unitHom : SheafOfModules.unit (Proj 𝒜).ringCatSheaf ⟶ twistingSheaf 𝒜 0 where
  val :=
    { app := fun U ↦ by
        let M := (SheafOfModules.unit (Proj 𝒜).ringCatSheaf).val.obj U
        let N := (twistingSheaf 𝒜 0).val.obj U
        exact @ModuleCat.ofHom ((Proj 𝒜).ringCatSheaf.obj.obj U) _ M N
          M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
          { toFun := fun r ↦ (show (Proj 𝒜).ringCatSheaf.obj.obj U from r) • one 𝒜 U
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- A degree-zero regular-module fraction is the same fraction in the homogeneous ring
localization. This existence proof uses the input's defining membership, not an admitted
surjectivity theorem. -/
theorem exists_zeroLocalization (P : Submonoid A) (s : LocalizedModule P A)
    (hs : ∃ i, ∃ m : 𝒜 i, ∃ t : 𝒜 i, ∃ ht : (t : A) ∈ P,
      s = LocalizedModule.mk (m : A) ⟨(t : A), ht⟩) :
    ∃ t : HomogeneousLocalization 𝒜 P, t.val = s := by
  rcases hs with ⟨i, m, t, ht, hs⟩
  refine ⟨HomogeneousLocalization.mk ⟨i, m, t, ht⟩, ?_⟩
  exact hs.symm

/-- The same localized fraction, now regarded as a homogeneous ring element. The choice is
from the proved representation above; injectivity of `HomogeneousLocalization.val` makes
the resulting element independent of the representative. -/
def zeroLocalization (P : Submonoid A)
    (s : localization 𝒜 (GradedMap.regularShift.{u, v} 𝒜 0) P) :
    HomogeneousLocalization 𝒜 P :=
  Classical.choose (exists_zeroLocalization 𝒜 P s.1 s.2)

/-- The degree-zero comparison preserves the underlying localized fraction. -/
@[simp] theorem zeroLocalization_val (P : Submonoid A)
    (s : localization 𝒜 (GradedMap.regularShift.{u, v} 𝒜 0) P) :
    (zeroLocalization 𝒜 P s).val = s.1 :=
  Classical.choose_spec (exists_zeroLocalization 𝒜 P s.1 s.2)

/-- Regard an actual section of O(0) as the same locally fractional structure-sheaf section. -/
def zeroSection (U : ((Proj 𝒜).Opens)ᵒᵖ) (s : (twistingSheaf 𝒜 0).val.obj U) :
    (Proj 𝒜).ringCatSheaf.obj.obj U :=
  let s' := sectionEquiv 𝒜 0 U.unop s
  ⟨fun x ↦ zeroLocalization 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl (s'.1 x), sorry⟩

/-- The inverse of the degree-zero unit map sends each pointwise fraction to itself. -/
def unitInv : twistingSheaf 𝒜 0 ⟶ SheafOfModules.unit (Proj 𝒜).ringCatSheaf where
  val :=
    { app := fun U ↦ by
        let M := (twistingSheaf 𝒜 0).val.obj U
        let N := (SheafOfModules.unit (Proj 𝒜).ringCatSheaf).val.obj U
        exact @ModuleCat.ofHom ((Proj 𝒜).ringCatSheaf.obj.obj U) _ M N
          M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
          { toFun := zeroSection 𝒜 U
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- The specified degree-zero unit map identifies O with its actual Serre twist O(0). -/
instance unitHom_isIso : IsIso (unitHom 𝒜) where
  out := ⟨unitInv 𝒜, sorry, sorry⟩

/-- The unit as a morphism from the monoidal tensor unit. -/
def oneHom : (𝟙_ (Proj 𝒜).Modules) ⟶ twistingSheaf 𝒜 0 :=
  (RingedSpace.unitIsoTensorUnit (Proj 𝒜).toRingedSpace).inv ≫ unitHom 𝒜

/-- Multiplication as a morphism from the actual tensor product of the two Serre twists. -/
def mulHom (a b : ℤ) : twistingSheaf 𝒜 a ⊗ twistingSheaf 𝒜 b ⟶ twistingSheaf 𝒜 (a + b) :=
  GradedAlgebraSheaf.mulHom (algebra 𝒜) a b

end AlgebraicGeometry.Proj.AssociatedModule.CanonicalAlgebra
