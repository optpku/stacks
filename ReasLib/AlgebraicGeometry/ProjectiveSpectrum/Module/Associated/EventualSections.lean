/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification.Tensor
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.ShiftedSections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.TwistedSections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Associated
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedSections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpen
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventual sections of associated module sheaves

This module constructs the canonical maps from the homogeneous pieces of an internally graded
module to the global sections of the corresponding tensor twists of its associated sheaf.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- The degree-`n` piece is the degree-zero piece of the grading shifted by `n`. -/
@[stacks 0B5R "degree as the zero piece of a shifted grading"]
theorem degree_eq_shift_zero (ℳ : ℤ → Submodule ℤ M) (n : ℤ) :
    ℳ n = GradedModule.shiftGrading ℳ n 0 := by
  simp [GradedModule.shiftGrading]

/-- View a homogeneous element as a degree-zero element of the translated grading, without
changing its underlying module element. -/
def toShiftZero (n : ℤ) : ℳ n →+ GradedModule.shiftGrading ℳ n 0 where
  toFun m := ⟨m, by rw [← degree_eq_shift_zero ℳ n]; exact m.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical section of the translated associated sheaf, given at each point by `m/1`. -/
@[stacks 0AG2 "canonical section of a shifted associated module"]
noncomputable def sectionMap (n : ℤ) : ℳ n →+ degree 𝒜 ℳ n :=
  (degreeZeroToGlobalSections 𝒜 (GradedModule.shiftGrading ℳ n)).toAddMonoidHom.comp
    (toShiftZero ℳ n)

/-- Evaluation of the canonical section is the homogeneous fraction with denominator one. -/
@[simp]
theorem sectionMap_atPoint (n : ℤ) (m : ℳ n) (x : (⊤ : (Proj 𝒜).Opens)) :
    (((sectionMap 𝒜 ℳ n m).1 x).1 :
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M) =
        LocalizedModule.mk (m : M) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) := rfl

/-- On a positive-degree standard open, the canonical shifted section is the fraction `m/1`.
The numerator is regarded as degree zero in the translated grading. -/
theorem sectionMap_away {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n : ℤ) (m : ℳ n) :
    restrict 𝒜 (GradedModule.shiftGrading ℳ n) le_top (sectionMap 𝒜 ℳ n m) =
      awaySection 𝒜 (GradedModule.shiftGrading ℳ n) f hd
        ⟨LocalizedModule.mk (m : M) (1 : Submonoid.powers (f : A)),
          HomogeneousLocalization.Module.mk_mem_degreeZeroPart 𝒜
            (nonnegativeGrading (GradedModule.shiftGrading ℳ n))
            (Submonoid.powers (f : A)) (toShiftZero ℳ n m)
            (1 : 𝒜 0) (by simp)⟩ :=
  degreeZeroToGlobalSections_away 𝒜 (GradedModule.shiftGrading ℳ n) f hd
    (toShiftZero ℳ n m)

/-- The sheaves associated to all translated module gradings, equipped with the canonical maps
from the corresponding homogeneous pieces to global sections. -/
@[stacks 0B5R "presentation of shifted associated sheaves"]
noncomputable def presentation :
    Proj.AssociatedModule.Presentation 𝒜 (fun n : ℤ ↦ (ℳ n : Type u)) :=
  Proj.AssociatedModule.Presentation.ofFamily
    (fun n : ℤ ↦ sheaf 𝒜 (GradedModule.shiftGrading ℳ n))
    (sectionMap 𝒜 ℳ)

/-- The canonical presentation uses exactly the associated sheaf of the translated grading. -/
@[simp]
theorem presentation_associatedTwist (n : ℤ) :
    (presentation 𝒜 ℳ).associatedTwist n =
      sheaf 𝒜 (GradedModule.shiftGrading ℳ n) := rfl

/-- The canonical presentation uses the explicit fraction section map. -/
@[simp]
theorem presentation_sectionMap (n : ℤ) :
    (presentation 𝒜 ℳ).sectionMap n = sectionMap 𝒜 ℳ n := rfl

-- Expose the existing canonical action through the presentation projection locally. No second
-- choice of homogeneous action is registered for arbitrary presentations.
local instance presentationGmodule [DirectSum.Decomposition ℳ] :
    DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ((presentation 𝒜 ℳ).associatedTwist n, ⊤)) :=
  instGmodule 𝒜 ℳ

/-- The actual fraction maps respect the canonical homogeneous action on shifted sections. -/
@[stacks 01MR "the canonical shifted-section presentation is graded"]
theorem presentation_isGraded [DirectSum.Decomposition ℳ] :
    (presentation 𝒜 ℳ).IsGraded := sorry

/-- The canonical graded map to shifted associated-sheaf sections. Both actions are induced by
the given graded module and homogeneous multiplication; no presentation or action is supplied
by the caller. -/
@[stacks 01MR "canonical graded associated-module section map"]
noncomputable def gradedMap [DirectSum.Decomposition ℳ] :
    (⨁ n : ℤ, ℳ n) →ₗ[(⨁ d : ℕ, 𝒜 d)] (⨁ n : ℤ, degree 𝒜 ℳ n) :=
  Presentation.gradedMap (fun n : ℤ ↦ (ℳ n : Type u))
    (presentation 𝒜 ℳ) (presentation_isGraded 𝒜 ℳ)

/-- On a homogeneous summand the canonical graded map is the fraction section in that degree. -/
@[simp]
theorem gradedMap_of [DirectSum.Decomposition ℳ] (n : ℤ) (m : ℳ n) :
    gradedMap 𝒜 ℳ (DirectSum.of (fun i : ℤ ↦ (ℳ i : Type u)) n m) =
      DirectSum.of (degree 𝒜 ℳ) n (sectionMap 𝒜 ℳ n m) :=
  Presentation.gradedMap_of (fun i : ℤ ↦ (ℳ i : Type u))
    (presentation 𝒜 ℳ) (presentation_isGraded 𝒜 ℳ) n m

/-- The actual tensor twist `M̃ ⊗ 𝒪(n)`, constructed by sheafifying the pointwise tensor
product. This uses the existing module-sheafification tensor owner. -/
abbrev tensorTwistSheaf (n : ℤ) : (Proj 𝒜).Modules :=
  ModuleSheafification.tensorObj (Proj 𝒜).sheaf
    (sheaf 𝒜 ℳ).val (twistingSheaf 𝒜 n).val

/-- The bilinear universal property identifies `tensorTwistSheaf` as the tensor product of the
actual associated sheaf and the actual twisting sheaf. Both directions are explicit maps. -/
def tensorTwistSheafHomEquiv (n : ℤ) (H : (Proj 𝒜).Modules) :
    (tensorTwistSheaf 𝒜 ℳ n ⟶ H) ≃
      PresheafOfModules.BilinearMap (Proj 𝒜).sheaf.obj
        (sheaf 𝒜 ℳ).val (twistingSheaf 𝒜 n).val H.val :=
  (ModuleSheafification.tensorHomEquiv (Proj 𝒜).sheaf H).trans
    (PresheafOfModules.BilinearMap.homEquiv
      (R := (Proj 𝒜).sheaf.obj) (F := (sheaf 𝒜 ℳ).val)
      (G := (twistingSheaf 𝒜 n).val) (H := H.val)).symm

/-- The pure tensor section given directly by the sheafification unit. -/
def tensorPureSection (n : ℤ) (U : ((Proj 𝒜).Opens)ᵒᵖ)
    (s : (sheaf 𝒜 ℳ).val.obj U) (t : (twistingSheaf 𝒜 n).val.obj U) :
    (tensorTwistSheaf 𝒜 ℳ n).val.obj U :=
  (ModuleSheafification.tensorUnitToVal (Proj 𝒜).sheaf
    (sheaf 𝒜 ℳ).val (twistingSheaf 𝒜 n).val).app U (s ⊗ₜ t)

/-- Global sections of the actual tensor twist. -/
abbrev tensorDegree (n : ℤ) : Type u := Γ(tensorTwistSheaf 𝒜 ℳ n, ⊤)

/-- Homogeneous multiplication on the twisting factor, followed by pointwise tensoring and
sheafification, gives the canonical action between tensor twists. -/
def tensorActionMap {d : ℕ} (a : 𝒜 d) (n : ℤ) :
    tensorTwistSheaf 𝒜 ℳ n ⟶ tensorTwistSheaf 𝒜 ℳ ((d : ℤ) + n) :=
  ModuleSheafification.tensorMap (Proj 𝒜).sheaf
    (𝟙 (sheaf 𝒜 ℳ).val) (Proj.TwistedSections.twistMap 𝒜 a n).val

/-- The canonical homogeneous action on sections of the sheafified tensor twists. -/
def tensorSmul {d : ℕ} {n : ℤ} (a : 𝒜 d) (s : tensorDegree 𝒜 ℳ n) :
    tensorDegree 𝒜 ℳ ((d : ℤ) + n) :=
  (Scheme.Modules.globalSectionsMap (tensorActionMap 𝒜 ℳ a n)).hom s

/-- The explicit tensor action defines the canonical graded module on tensor-twist sections. -/
instance instTensorGmodule :
    DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) (tensorDegree 𝒜 ℳ) where
  smul := fun a s ↦ tensorSmul 𝒜 ℳ a s
  one_smul := sorry
  mul_smul := sorry
  smul_add := sorry
  smul_zero := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The canonical comparison from the actual tensor twist to the shifted associated sheaf.
It descends the explicit localized tensor pairing, then applies the tensor right-unit map. -/
def tensorShiftComparison [DirectSum.Decomposition ℳ] (n : ℤ) :
    tensorTwistSheaf 𝒜 ℳ n ⟶ sheaf 𝒜 (GradedModule.shiftGrading ℳ n) :=
  ModuleSheafification.tensorLift (Proj 𝒜).sheaf
      (sheaf 𝒜 (GradedModule.TensorProduct.grading A ℳ
        (GradedModule.shiftGrading (DirectSum.Decomposition.natToIntGrading 𝒜) n)))
      (Proj.AssociatedModule.Tensor.bilinear 𝒜 ℳ
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) n)).toHom ≫
    map 𝒜
      (GradedModule.TensorProduct.gradingFor A 𝒜 ℳ
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) n))
      (GradedModule.shiftGrading ℳ n) (TensorProduct.rid A M).toLinearMap
      (ShiftComparison.tensorRid_mapsTo 𝒜 ℳ n)

/-- On pure sections the comparison is the localized tensor pairing followed by the ordinary
module right-unit map, fixing the canonical meaning of the shift comparison. -/
theorem tensorShiftComparison_pure [DirectSum.Decomposition ℳ]
    (n : ℤ) (U : ((Proj 𝒜).Opens)ᵒᵖ)
    (s : (sheaf 𝒜 ℳ).val.obj U) (t : (twistingSheaf 𝒜 n).val.obj U) :
    ((tensorShiftComparison 𝒜 ℳ n).val.app U).hom (tensorPureSection 𝒜 ℳ n U s t) =
      mapSection 𝒜
        (GradedModule.TensorProduct.gradingFor A 𝒜 ℳ
          (GradedModule.shiftGrading
            (DirectSum.Decomposition.natToIntGrading 𝒜) n))
        (GradedModule.shiftGrading ℳ n) (TensorProduct.rid A M).toLinearMap
        (ShiftComparison.tensorRid_mapsTo 𝒜 ℳ n) U.unop
        (Proj.AssociatedModule.Tensor.sectionValue 𝒜 ℳ
          (GradedModule.shiftGrading
            (DirectSum.Decomposition.natToIntGrading 𝒜) n) U.unop s t) := sorry

/-- Under the degree-one standard-open cover the canonical shift comparison is an isomorphism.
This property is not used to extract any of the section-map data below. -/
theorem tensorShiftComparison_isIso [DirectSum.Decomposition ℳ]
    (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) :
    IsIso (tensorShiftComparison 𝒜 ℳ n) := sorry

/-- On `D₊(f)`, the fraction `f^((-n).toNat) m / f^(n.toNat)` has degree zero. -/
theorem tensorModuleFraction_mem (n : ℤ) (f : 𝒜 1) (m : ℳ n) :
    LocalizedModule.mk ((f : A) ^ (-n).toNat • (m : M))
        (⟨(f : A) ^ n.toNat, ⟨n.toNat, rfl⟩⟩ : Submonoid.powers (f : A)) ∈
      away 𝒜 ℳ f := sorry

/-- The explicit degree-zero fraction `m/f^n`, also for negative `n`. -/
def tensorModuleFraction (n : ℤ) (f : 𝒜 1) (m : ℳ n) : away 𝒜 ℳ f :=
  ⟨LocalizedModule.mk ((f : A) ^ (-n).toNat • (m : M))
      (⟨(f : A) ^ n.toNat, ⟨n.toNat, rfl⟩⟩ : Submonoid.powers (f : A)),
    tensorModuleFraction_mem 𝒜 ℳ n f m⟩

/-- The fraction `f^(n.toNat)/f^((-n).toNat)` has degree zero in the shifted regular grading. -/
theorem tensorTwistFraction_mem (n : ℤ) (f : 𝒜 1) :
    LocalizedModule.mk ((f : A) ^ n.toNat)
        (⟨(f : A) ^ (-n).toNat, ⟨(-n).toNat, rfl⟩⟩ : Submonoid.powers (f : A)) ∈
      away 𝒜 (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) n) f := sorry

/-- The explicit local generator `f^n` of `𝒪(n)` on a degree-one standard open. -/
def tensorTwistFraction (n : ℤ) (f : 𝒜 1) :
    away 𝒜 (GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading 𝒜) n) f :=
  ⟨LocalizedModule.mk ((f : A) ^ n.toNat)
      (⟨(f : A) ^ (-n).toNat, ⟨(-n).toNat, rfl⟩⟩ : Submonoid.powers (f : A)),
    tensorTwistFraction_mem 𝒜 n f⟩

/-- The local tensor section `(m/f^n) ⊗ f^n` on `D₊(f)`. -/
def tensorSectionOnBasicOpen (n : ℤ) (f : 𝒜 1) :
    ℳ n →+ Γ(tensorTwistSheaf 𝒜 ℳ n, Proj.basicOpen 𝒜 (f : A)) where
  toFun m := tensorPureSection 𝒜 ℳ n (op (Proj.basicOpen 𝒜 (f : A)))
    (awaySection 𝒜 ℳ f (by decide) (tensorModuleFraction 𝒜 ℳ n f m))
    (awaySection 𝒜 (GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading 𝒜) n) f (by decide)
      (tensorTwistFraction 𝒜 n f))
  map_zero' := sorry
  map_add' := sorry

/-- Inclusion of a degree-one standard open into `Proj`. -/
abbrev tensorSectionCoverι (f : 𝒜 1) :
    Proj.basicOpen 𝒜 (f : A) ⟶ (⊤ : (Proj 𝒜).Opens) := homOfLE le_top

/-- The degree-one covering assumption supplies exactly the cover used for tensor sections. -/
theorem tensorSectionCover_mem (hcover : Proj.degreeOpen 𝒜 1 = ⊤) :
    Sieve.ofArrows (fun f : 𝒜 1 ↦ Proj.basicOpen 𝒜 (f : A))
        (tensorSectionCoverι 𝒜) ∈
      Opens.grothendieckTopology (Proj 𝒜) (⊤ : (Proj 𝒜).Opens) := by
  intro x hx
  have hx' : x ∈ Proj.degreeOpen 𝒜 1 := by simpa only [hcover] using hx
  obtain ⟨f, hf⟩ := Opens.mem_iSup.mp hx'
  obtain ⟨hf, hxf⟩ := Opens.mem_iSup.mp hf
  exact ⟨Proj.basicOpen 𝒜 f, homOfLE le_top,
    Sieve.ofArrows_mk _ _ (⟨f, hf⟩ : 𝒜 1), hxf⟩

/-- The explicit local tensor maps agree on every overlap. -/
theorem tensorSectionOnBasicOpen_compatible (n : ℤ) (m : ℳ n)
    {W : (Proj 𝒜).Opens} {f g : 𝒜 1}
    (a : W ⟶ Proj.basicOpen 𝒜 (f : A)) (b : W ⟶ Proj.basicOpen 𝒜 (g : A))
    (hab : a ≫ tensorSectionCoverι 𝒜 f = b ≫ tensorSectionCoverι 𝒜 g) :
    (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map a.op
        (tensorSectionOnBasicOpen 𝒜 ℳ n f m) =
      (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map b.op
        (tensorSectionOnBasicOpen 𝒜 ℳ n g m) := sorry

/-- The degree-one cover as a cover of the opens site. -/
def tensorSectionCover (hcover : Proj.degreeOpen 𝒜 1 = ⊤) :
    (Opens.grothendieckTopology (Proj 𝒜)).Cover (⊤ : (Proj 𝒜).Opens) :=
  ⟨_, tensorSectionCover_mem 𝒜 hcover⟩

/-- The specified local tensor sections as a concrete matching family. A sieve arrow is
represented by a factorization through a degree-one standard open; the factorization is
supplied by the proved sieve-membership API. The compatibility field is a property of this
explicit family, not an existence assertion used to choose a global section. -/
def tensorSectionMatchingFamily (hcover : Proj.degreeOpen 𝒜 1 = ⊤)
    (n : ℤ) (m : ℳ n) :
    Meq (tensorTwistSheaf 𝒜 ℳ n).val.presheaf (tensorSectionCover 𝒜 hcover) := by
  let chart : (tensorSectionCover 𝒜 hcover).Arrow → 𝒜 1 := fun I ↦
    Sieve.ofArrows.i (Y := fun f : 𝒜 1 ↦ Proj.basicOpen 𝒜 (f : A))
      (f := tensorSectionCoverι 𝒜) I.hf
  let chartMap (I : (tensorSectionCover 𝒜 hcover).Arrow) :
      I.Y ⟶ Proj.basicOpen 𝒜 (chart I : A) :=
    Sieve.ofArrows.h (Y := fun f : 𝒜 1 ↦ Proj.basicOpen 𝒜 (f : A))
      (f := tensorSectionCoverι 𝒜) I.hf
  have hfac (I : (tensorSectionCover 𝒜 hcover).Arrow) :
      chartMap I ≫ tensorSectionCoverι 𝒜 (chart I) = I.f :=
    Sieve.ofArrows.fac I.hf
  refine ⟨fun I ↦ (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map (chartMap I).op
    (tensorSectionOnBasicOpen 𝒜 ℳ n (chart I) m), ?_⟩
  intro I
  have hab :
      (I.r.g₁ ≫ chartMap I.fst) ≫ tensorSectionCoverι 𝒜 (chart I.fst) =
        (I.r.g₂ ≫ chartMap I.snd) ≫ tensorSectionCoverι 𝒜 (chart I.snd) := by
    simpa only [Category.assoc, hfac] using I.r.w
  simpa only [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply] using
    (tensorSectionOnBasicOpen_compatible 𝒜 ℳ n m
      (I.r.g₁ ≫ chartMap I.fst) (I.r.g₂ ≫ chartMap I.snd) hab)

/-- Any factorization of a sieve arrow through a degree-one standard open computes the same
matching-family value. In particular the value is independent of the selected chart. -/
theorem tensorSectionMatchingFamily_apply (hcover : Proj.degreeOpen 𝒜 1 = ⊤)
    (n : ℤ) (m : ℳ n) (I : (tensorSectionCover 𝒜 hcover).Arrow) (f : 𝒜 1)
    (a : I.Y ⟶ Proj.basicOpen 𝒜 (f : A))
    (ha : a ≫ tensorSectionCoverι 𝒜 f = I.f) :
    tensorSectionMatchingFamily 𝒜 ℳ hcover n m I =
      (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map a.op
        (tensorSectionOnBasicOpen 𝒜 ℳ n f m) := by
  let cf : 𝒜 1 := Sieve.ofArrows.i
    (Y := fun g : 𝒜 1 ↦ Proj.basicOpen 𝒜 (g : A)) (f := tensorSectionCoverι 𝒜) I.hf
  let ca : I.Y ⟶ Proj.basicOpen 𝒜 (cf : A) := Sieve.ofArrows.h
    (Y := fun g : 𝒜 1 ↦ Proj.basicOpen 𝒜 (g : A)) (f := tensorSectionCoverι 𝒜) I.hf
  have hfac : ca ≫ tensorSectionCoverι 𝒜 cf = I.f := Sieve.ofArrows.fac I.hf
  change (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map ca.op
    (tensorSectionOnBasicOpen 𝒜 ℳ n cf m) = _
  exact tensorSectionOnBasicOpen_compatible 𝒜 ℳ n m ca a (hfac.trans ha.symm)

/-- Matching-family values commute with every restriction of sieve arrows. -/
theorem tensorSectionMatchingFamily_restrict (hcover : Proj.degreeOpen 𝒜 1 = ⊤)
    (n : ℤ) (m : ℳ n) (I : (tensorSectionCover 𝒜 hcover).Arrow)
    {W : (Proj 𝒜).Opens} (a : W ⟶ I.Y) :
    (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map a.op
        (tensorSectionMatchingFamily 𝒜 ℳ hcover n m I) =
      tensorSectionMatchingFamily 𝒜 ℳ hcover n m (I.precomp a) := by
  have h := ((tensorSectionMatchingFamily 𝒜 ℳ hcover n m).condition
    (GrothendieckTopology.Cover.Relation.mk' (I.precompRelation a))).symm
  change (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map a.op
      (tensorSectionMatchingFamily 𝒜 ℳ hcover n m I) =
    (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map (𝟙 W).op
      (tensorSectionMatchingFamily 𝒜 ℳ hcover n m (I.precomp a)) at h
  rw [op_id, (tensorTwistSheaf 𝒜 ℳ n).val.presheaf.map_id (op W)] at h
  exact h

/-- Stacks `0AG3`: the explicit matching family gives a section of the plus construction by
the multiequalizer and colimit maps. The canonical plus lift of the actual tensor sheaf then
gives its global section. No global section is selected from an admitted existence theorem. -/
@[stacks 0AG3 "canonical map to actual tensor-twist sections"]
def tensorSectionMap (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) :
    ℳ n →+ Γ(tensorTwistSheaf 𝒜 ℳ n, ⊤) where
  toFun m := ((Opens.grothendieckTopology (Proj 𝒜)).plusLift
      (𝟙 (tensorTwistSheaf 𝒜 ℳ n).val.presheaf)
      (tensorTwistSheaf 𝒜 ℳ n).isSheaf).app (op ⊤)
    (GrothendieckTopology.Plus.mk (tensorSectionMatchingFamily 𝒜 ℳ hcover n m))
  map_zero' := sorry
  map_add' := sorry

/-- The glued map restricts to `(m/f^n) ⊗ f^n` on every degree-one standard open. -/
theorem tensorSectionMap_basicOpen (hcover : Proj.degreeOpen 𝒜 1 = ⊤)
    (n : ℤ) (f : 𝒜 1) (m : ℳ n) :
    (tensorTwistSheaf 𝒜 ℳ n).val.map (tensorSectionCoverι 𝒜 f).op
        (tensorSectionMap 𝒜 ℳ hcover n m) =
      tensorSectionOnBasicOpen 𝒜 ℳ n f m := sorry

/-- The actual canonical shift comparison sends the tensor section to the original `m/1`
section. This identifies the glued construction with transport through the comparison. -/
theorem tensorSectionMap_comparison [DirectSum.Decomposition ℳ]
    (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) (m : ℳ n) :
    (Scheme.Modules.globalSectionsMap (tensorShiftComparison 𝒜 ℳ n)).hom
        (tensorSectionMap 𝒜 ℳ hcover n m) = sectionMap 𝒜 ℳ n m := sorry

/-- The tensor section is the unique preimage of `m/1` under the canonical comparison. -/
theorem tensorSectionMap_unique [DirectSum.Decomposition ℳ]
    (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) (m : ℳ n)
    (s : Γ(tensorTwistSheaf 𝒜 ℳ n, ⊤))
    (hs : (Scheme.Modules.globalSectionsMap (tensorShiftComparison 𝒜 ℳ n)).hom s =
      sectionMap 𝒜 ℳ n m) : s = tensorSectionMap 𝒜 ℳ hcover n m := sorry

/-- The canonical presentation of the actual tensor twists under the degree-one cover. -/
def tensorPresentation (hcover : Proj.degreeOpen 𝒜 1 = ⊤) :
    Presentation 𝒜 (fun n : ℤ ↦ (ℳ n : Type u)) :=
  Presentation.ofFamily (tensorTwistSheaf 𝒜 ℳ) (tensorSectionMap 𝒜 ℳ hcover)

/-- The tensor presentation has the actual sheafified tensor product in each degree. -/
@[simp]
theorem tensorPresentation_associatedTwist (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) :
    (tensorPresentation 𝒜 ℳ hcover).associatedTwist n = tensorTwistSheaf 𝒜 ℳ n := rfl

/-- The tensor presentation uses the specified local tensor sections and their gluing. -/
@[simp]
theorem tensorPresentation_sectionMap (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) :
    (tensorPresentation 𝒜 ℳ hcover).sectionMap n = tensorSectionMap 𝒜 ℳ hcover n := rfl

local instance tensorPresentationGmodule (hcover : Proj.degreeOpen 𝒜 1 = ⊤) :
    DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ((tensorPresentation 𝒜 ℳ hcover).associatedTwist n, ⊤)) :=
  instTensorGmodule 𝒜 ℳ

/-- The explicit tensor-section maps respect canonical homogeneous multiplication. -/
theorem tensorPresentation_isGraded (hcover : Proj.degreeOpen 𝒜 1 = ⊤) :
    (tensorPresentation 𝒜 ℳ hcover).IsGraded := sorry

/-- Stacks `0AG4`: the graded map to actual tensor-twist sections, with the canonical action. -/
@[stacks 0AG4 "canonical graded map to actual tensor-twist sections"]
def tensorGradedMap (hcover : Proj.degreeOpen 𝒜 1 = ⊤) :
    (⨁ n : ℤ, ℳ n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, tensorDegree 𝒜 ℳ n) :=
  Presentation.gradedMap (fun n : ℤ ↦ (ℳ n : Type u))
    (tensorPresentation 𝒜 ℳ hcover) (tensorPresentation_isGraded 𝒜 ℳ hcover)

/-- On a homogeneous summand the tensor graded map uses the specified tensor section. -/
@[simp]
theorem tensorGradedMap_of (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) (m : ℳ n) :
    tensorGradedMap 𝒜 ℳ hcover (DirectSum.of (fun i : ℤ ↦ (ℳ i : Type u)) n m) =
      DirectSum.of (tensorDegree 𝒜 ℳ) n
        (tensorSectionMap 𝒜 ℳ hcover n m) :=
  Presentation.gradedMap_of (fun i : ℤ ↦ (ℳ i : Type u))
    (tensorPresentation 𝒜 ℳ hcover) (tensorPresentation_isGraded 𝒜 ℳ hcover) n m

/-- Transport the shifted section map along a supplied comparison. This general transport
helper is independent of the canonical tensor construction `tensorSectionMap`. -/
noncomputable def toTensorTwist
    (comparisonIso : ∀ n : ℤ,
      ProjTwistFamily.tensorTwist (twistingSheaf 𝒜) (sheaf 𝒜 ℳ) n ≅
        sheaf 𝒜 (GradedModule.shiftGrading ℳ n))
    (n : ℤ) :
    AddCommGrpCat.of (ℳ n) ⟶
      AddCommGrpCat.of
        (Γ(ProjTwistFamily.tensorTwist (twistingSheaf 𝒜) (sheaf 𝒜 ℳ) n, ⊤)) :=
  AddCommGrpCat.ofHom <|
    Proj.AssociatedModule.Presentation.sectionMapOfIso
      (presentation 𝒜 ℳ) (comparisonIso n)

/-- For a finite graded module over a finite-type degree-one-generated graded ring with
Noetherian degree-zero part, the canonical maps to twisted global sections are isomorphisms in
all sufficiently large degrees. -/
@[stacks 0AG7 "eventual isomorphism to tensor-twist sections"]
theorem toTensorTwist_eventually_isIso
    [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1)
    [DirectSum.Decomposition ℳ] [Module.Finite A M]
    (comparisonIso : ∀ n : ℤ,
      ProjTwistFamily.tensorTwist (twistingSheaf 𝒜) (sheaf 𝒜 ℳ) n ≅
        sheaf 𝒜 (GradedModule.shiftGrading ℳ n)) :
    ∃ b : ℤ, ∀ n : ℤ, b ≤ n →
      IsIso (toTensorTwist 𝒜 ℳ comparisonIso n) := sorry

end AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections

namespace AlgebraicGeometry

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- The actual associated sheaf of the grading translated by `n`. -/
abbrev projAssociatedTwist (n : ℤ) : (Proj 𝒜).Modules :=
  Proj.AssociatedModule.sheaf 𝒜 (GradedModule.shiftGrading ℳ n)

/-- The actual associated sheaf of the given graded module. -/
abbrev projAssociatedModuleSheaf : (Proj 𝒜).Modules :=
  Proj.AssociatedModule.sheaf 𝒜 ℳ

/-- The canonical graded map to sections of the actual shifted associated sheaves. -/
abbrev gradedModuleToProjAssociatedTwistGlobalSectionsMap [DirectSum.Decomposition ℳ] :
    (⨁ n : ℤ, ℳ n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, Γ(projAssociatedTwist 𝒜 ℳ n, ⊤)) :=
  Proj.AssociatedModule.ShiftedSections.gradedMap 𝒜 ℳ

end AlgebraicGeometry
