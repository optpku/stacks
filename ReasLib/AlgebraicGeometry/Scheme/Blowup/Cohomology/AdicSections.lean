/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.QuotientTwist

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The nonnegative exceptional tensor power maps to the structure sheaf by
tensoring its ideal inclusion. -/
noncomputable def exceptionalPowerInclusion
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] :
    (q : ℕ) → Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule q ⟶
      SheafOfModules.unit X.ringCatSheaf
  | 0 => InvertiblePower.evalZeroIso _ _ |>.hom
  | q + 1 =>
      (InvertiblePower.evalRightSuccIso (exceptionalIdeal I p).toModule
        (SheafOfModules.unit X.ringCatSheaf) (q : ℤ)).inv ≫
      (@tensorHom _ _ (Scheme.Modules.instMonoidalCategory X).toMonoidalCategoryStruct _ _ _ _
        (exceptionalPowerInclusion I p q) (exceptionalIdeal I p).toSubobject.arrow) ≫
      (@tensorHom _ _ (Scheme.Modules.instMonoidalCategory X).toMonoidalCategoryStruct _ _ _ _
        (𝟙 _) (RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom) ≫
      (@rightUnitor _ _ (Scheme.Modules.instMonoidalCategory X).toMonoidalCategoryStruct _).hom

/-- Nonnegative powers of an invertible ideal retain a monomorphic inclusion. -/
instance exceptionalPowerInclusion_mono
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℕ) :
    Mono (exceptionalPowerInclusion I p q) := sorry

/-- Pullback of the ordinary ideal-power inclusion into the structure sheaf. -/
noncomputable def pulledIdealPowerInclusion
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) (q : ℕ) :
    (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
        (ModuleCat.of A ↥(I ^ q)) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullback p).map
      (Spec.tildeIdeal.ι (R := CommRingCat.of A) (I ^ q) ≫
        (RingedSpace.unitIsoTensorUnit (Spec (CommRingCat.of A)).toRingedSpace).hom) ≫
    (Scheme.Modules.pullbackUnitIso p).hom ≫
    (RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv

/-- The affine ideal-sheaf module agrees with the concrete tilde ideal
subobject, retaining the same inclusion into the structure sheaf. -/
theorem affineIdealSubobject_eq
    {A : Type u} [CommRing A] (I : Ideal A) :
    (Scheme.idealSheafDataOfIdealOnSpec I).toSubobject =
      Spec.tildeIdeal.subobject (R := CommRingCat.of A) I := sorry

/-- The first exceptional factor is constructed from the concrete tilde
ideal comparison and the image factor of the pulled-back inclusion. -/
noncomputable def idealToExceptionalIdeal
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) :
    (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj (ModuleCat.of A I) ⟶
      (exceptionalIdeal I p).toModule :=
  let J := Scheme.idealSheafDataOfIdealOnSpec I
  (Scheme.Modules.pullback p).map
      ((Spec.tildeIdeal.moduleIso (R := CommRingCat.of A) I).inv ≫
        eqToHom (congrArg Subobject.underlying.obj (affineIdealSubobject_eq I).symm)) ≫
    RingedSpace.IdealSubobject.pullbackFactor J.toSubobject p.toShHom ≫
    eqToHom (congrArg Subobject.underlying.obj (J.toSubobject_comap p).symm)

/-- The image-based first factor composes with the exceptional ideal inclusion
to the usual pulled-back affine ideal inclusion. -/
theorem idealToExceptionalIdeal_fac
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) :
    idealToExceptionalIdeal I p ≫ (exceptionalIdeal I p).toSubobject.arrow =
      (Scheme.Modules.pullback p).map (Spec.tildeIdeal.ι (R := CommRingCat.of A) I) ≫
        SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom := sorry

/-- The tensor multiplication of ideal elements lands in the next ideal power. -/
theorem idealPowerProduct_mem
    {A : Type u} [CommRing A] (I : Ideal A) (q : ℕ)
    (x : TensorProduct A I ↥(I ^ q)) :
    (LinearMap.mul' A A)
      (TensorProduct.map I.subtype (I ^ q).subtype x) ∈ I ^ (q + 1) := sorry

/-- Multiplication on the tensor of two consecutive ideal factors, with an
explicit scalar multiplication formula and a subtype-valued codomain. -/
noncomputable def idealPowerProduct
    {A : Type u} [CommRing A] (I : Ideal A) (q : ℕ) :
    ModuleCat.of A I ⊗ ModuleCat.of A ↥(I ^ q) ⟶ ModuleCat.of A ↥(I ^ (q + 1)) :=
  ModuleCat.ofHom
    (((LinearMap.mul' A A).comp (TensorProduct.map I.subtype (I ^ q).subtype)).codRestrict
      (I ^ (q + 1)) (idealPowerProduct_mem I q))

/-- Tensor multiplication sends a pure tensor to the product of its two scalars. -/
theorem idealPowerProduct_tmul
    {A : Type u} [CommRing A] (I : Ideal A) (q : ℕ)
    (a : I) (b : ↥(I ^ q)) :
    ((idealPowerProduct I q).hom (a ⊗ₜ[A] b) : A) = (a : A) * (b : A) := sorry

/-- Ideal multiplication is surjective onto the product ideal. -/
instance idealPowerProduct_epi
    {A : Type u} [CommRing A] (I : Ideal A) (q : ℕ) : Epi (idealPowerProduct I q) := sorry

/-- The associated-module functor preserves the quotient presentation of an ideal power. -/
instance pulledIdealPowerProduct_epi
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) (q : ℕ) :
    Epi ((Scheme.Modules.affineBaseModuleAssociatedFunctor A p).map
      (idealPowerProduct I q)) := sorry

/-- Map the tensor generators of the next ideal power using the first-degree
image factor and the already constructed preceding-degree factor. -/
noncomputable def exceptionalPowerProductMap
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℕ)
    (f : (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
      (ModuleCat.of A ↥(I ^ q)) ⟶ Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule q) :
    (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
      (ModuleCat.of A I ⊗ ModuleCat.of A ↥(I ^ q)) ⟶
        Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule (q + 1) :=
  (Scheme.Modules.pullback p).map
      (tilde.Tensor.comparison (R := CommRingCat.of A) (ModuleCat.of A I)
        (ModuleCat.of A ↥(I ^ q))) ≫
    Scheme.Modules.pullbackTensorComparison p (tilde (ModuleCat.of A I))
      (tilde (ModuleCat.of A ↥(I ^ q))) ≫
    (idealToExceptionalIdeal I p ⊗ₘ f) ≫ (β_ _ _).hom ≫
    (InvertiblePower.evalRightSuccIso (exceptionalIdeal I p).toModule
      (SheafOfModules.unit X.ringCatSheaf) q).hom

/-- The explicit generator map kills the relations in the ideal multiplication
presentation, provided the preceding factor respects the ideal inclusion. -/
theorem exceptionalPowerProductMap_relations
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℕ)
    (f : (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
      (ModuleCat.of A ↥(I ^ q)) ⟶ Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule q)
    (hf : f ≫ exceptionalPowerInclusion I p q = pulledIdealPowerInclusion I p q) :
    Limits.kernel.ι ((Scheme.Modules.affineBaseModuleAssociatedFunctor A p).map
      (idealPowerProduct I q)) ≫ exceptionalPowerProductMap I p q f = 0 := sorry

/-- The zero-degree factor is the unit identification. -/
theorem exceptionalPowerZero_fac
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] :
    (pulledIdealPowerInclusion I p 0 ≫ (InvertiblePower.evalZeroIso
      (exceptionalIdeal I p).toModule (SheafOfModules.unit X.ringCatSheaf)).inv) ≫
        exceptionalPowerInclusion I p 0 = pulledIdealPowerInclusion I p 0 := sorry

/-- Descending the explicit generator map preserves the ideal-inclusion equation. -/
theorem exceptionalPowerDesc_fac
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℕ)
    (f : (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
      (ModuleCat.of A ↥(I ^ q)) ⟶ Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule q)
    (hf : f ≫ exceptionalPowerInclusion I p q = pulledIdealPowerInclusion I p q) :
    Abelian.epiDesc ((Scheme.Modules.affineBaseModuleAssociatedFunctor A p).map
      (idealPowerProduct I q)) (exceptionalPowerProductMap I p q f)
        (exceptionalPowerProductMap_relations I p q f hf) ≫
      exceptionalPowerInclusion I p (q + 1) = pulledIdealPowerInclusion I p (q + 1) := sorry

/-- The unique factor of the pulled-back ideal-power inclusion through the
exceptional tensor power. Unlike an arbitrary Hom witness, its composite with
the monomorphic ideal inclusion is prescribed. -/
noncomputable def idealPowerToExceptionalPower
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℕ) :
    (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
        (ModuleCat.of A ↥(I ^ q)) ⟶
      Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule q :=
  let rec exceptionalPowerFactor :
      (r : ℕ) → {f : (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
        (ModuleCat.of A ↥(I ^ r)) ⟶
          Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule r //
        f ≫ exceptionalPowerInclusion I p r = pulledIdealPowerInclusion I p r}
    | 0 => ⟨pulledIdealPowerInclusion I p 0 ≫ (InvertiblePower.evalZeroIso
        (exceptionalIdeal I p).toModule (SheafOfModules.unit X.ringCatSheaf)).inv,
          exceptionalPowerZero_fac I p⟩
    | r + 1 =>
        let prev := exceptionalPowerFactor r
        ⟨Abelian.epiDesc ((Scheme.Modules.affineBaseModuleAssociatedFunctor A p).map
            (idealPowerProduct I r)) (exceptionalPowerProductMap I p r prev.val)
            (exceptionalPowerProductMap_relations I p r prev.val prev.property),
          exceptionalPowerDesc_fac I p r prev.val prev.property⟩
  (exceptionalPowerFactor q).val

/-- The recursively descended map sends the tensor multiplication generators to
the prescribed product of the first and preceding exceptional factors. -/
theorem idealPowerToExceptionalPower_succ
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℕ) :
    (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).map (idealPowerProduct I q) ≫
        idealPowerToExceptionalPower I p (q + 1) =
      exceptionalPowerProductMap I p q (idealPowerToExceptionalPower I p q) := sorry

/-- The exceptional-power factor recovers the pulled-back ideal inclusion. -/
theorem idealPowerToExceptionalPower_fac
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℕ) :
    idealPowerToExceptionalPower I p q ≫ exceptionalPowerInclusion I p q =
      pulledIdealPowerInclusion I p q := sorry

/-- The sheaf-level tensor comparison in nonnegative degree, using the ideal
factor and the symmetry that places the coefficient module first. -/
noncomputable def adicTensorToTwist
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℕ) :
    (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
        (ModuleCat.of A ↥(I ^ q) ⊗
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M) ⟶
      quotientModuleTwist I p M q :=
  let N := (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M
  (Scheme.Modules.pullback p).map
      (tilde.Tensor.comparison (R := CommRingCat.of A) (ModuleCat.of A ↥(I ^ q)) N) ≫
    Scheme.Modules.pullbackTensorComparison p (tilde (ModuleCat.of A ↥(I ^ q))) (tilde N) ≫
    (idealPowerToExceptionalPower I p q ⊗ₘ 𝟙 _) ≫ (β_ _ _).hom

/-- Converting affine-base sections to sections at the top open preserves scalars. -/
theorem affineSections_smul
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (a : A)
    (x : (Scheme.Modules.affineBaseModuleGlobalSectionsFunctor A p).obj F) :
    (a • x : (Scheme.Modules.affineBaseModuleGlobalSectionsFunctor A p).obj F) =
      (a • x : (ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap p)).obj
        (F.val.obj (Opposite.op ⊤))) := sorry

/-- The concrete identity-on-sections comparison followed by the canonical map
from global sections to their zeroth right derived functor. -/
noncomputable def affineSectionsToCohomologyZero
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) :
    (Scheme.Modules.affineBaseModuleGlobalSectionsFunctor A p).obj F ⟶
      Scheme.Hom.cohomology p F 0 :=
  let S : ModuleCat A := (Scheme.Modules.affineBaseModuleGlobalSectionsFunctor A p).obj F
  let T : ModuleCat A := (ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap p)).obj
    (F.val.obj (Opposite.op ⊤))
  let l : S →ₗ[A] T :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := affineSections_smul p F }
  (ConcreteCategory.ofHom (C := ModuleCat A) (X := S) (Y := T) l) ≫
    (ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap p)).map
      ((RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace ⊤).toRightDerivedZero.app F)

/-- The integer twist is reached from its nonnegative part by the canonical
downward transition. -/
theorem adicTwistDegree (q : ℤ) : (q.toNat : ℤ) - ((-q).toNat : ℤ) = q := sorry

/-- The tensor-presentation section map: transpose the sheaf tensor comparison, pass to
zeroth cohomology, and use the canonical transition for negative degrees. -/
noncomputable def canonicalAdicTensorSectionMap
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℤ) :
    (ModuleCat.of A ↥(I ^ q.toNat) ⊗
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M) ⟶
      Scheme.Hom.cohomology p (quotientModuleTwist I p M q) 0 :=
  (Scheme.Modules.affineBaseModuleAdjunction A p).homEquiv _ _
      (adicTensorToTwist I p M q.toNat) ≫
    affineSectionsToCohomologyZero p (quotientModuleTwist I p M q.toNat) ≫
    (Scheme.Hom.cohomologyFunctor p 0).map
      (canonicalTwistTransition I p M q.toNat (-q).toNat ≫
        eqToHom (congrArg (quotientModuleTwist I p M) (adicTwistDegree q)))

/-- In nonnegative degree the section map is the adjunction transpose of the
geometric tensor comparison followed by the degree-zero cohomology comparison. -/
theorem canonicalAdicTensorSectionMap_spec
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℕ) :
    canonicalAdicTensorSectionMap I p M q =
      (Scheme.Modules.affineBaseModuleAdjunction A p).homEquiv _ _
          (adicTensorToTwist I p M q) ≫
        affineSectionsToCohomologyZero p (quotientModuleTwist I p M q) := sorry

/-- A pure tensor is sent to the cohomology class of its geometric tensor
section, obtained from the ideal inclusion factor and the tilde-pullback unit. -/
theorem canonicalAdicTensorSectionMap_apply
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℕ)
    (a : ↥(I ^ q)) (m : (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M) :
    (canonicalAdicTensorSectionMap I p M q).hom (a ⊗ₜ[A] m) =
      (affineSectionsToCohomologyZero p (quotientModuleTwist I p M q)).hom
        (((Scheme.Modules.affineBaseModuleAdjunction A p).homEquiv _ _
          (adicTensorToTwist I p M q)).hom (a ⊗ₜ[A] m)) := sorry

/-- The tensor source transitions by inclusion of the larger ideal power,
leaving the coefficient module unchanged. -/
noncomputable def adicTensorInclusion
    {A : Type u} [CommRing A] (I : Ideal A)
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q r : ℕ) (h : r ≤ q) :
    (ModuleCat.of A ↥(I ^ q) ⊗
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M) ⟶
      (ModuleCat.of A ↥(I ^ r) ⊗
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M) :=
  ModuleCat.ofHom (Submodule.inclusion (Ideal.pow_le_pow_right h)) ⊗ₘ 𝟙 _

/-- The nonnegative degree difference used in the transition square. -/
theorem adicTensorDegree (q r : ℕ) : ((q + r : ℕ) : ℤ) - (r : ℤ) = q := sorry

/-- The adic section maps are natural with respect to the ideal-power inclusions and canonical
twist transitions. -/
theorem canonicalAdicTensorSectionMap_naturality
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q r : ℕ) :
    canonicalAdicTensorSectionMap I p M (q + r) ≫
        (Scheme.Hom.cohomologyFunctor p 0).map
          (canonicalTwistTransition I p M (q + r) r ≫
            eqToHom (congrArg (quotientModuleTwist I p M)
              (adicTensorDegree q r))) =
      adicTensorInclusion I M (q + r) q (Nat.le_add_right q r) ≫
        canonicalAdicTensorSectionMap I p M q := sorry

end AlgebraicGeometry.IsBlowup
