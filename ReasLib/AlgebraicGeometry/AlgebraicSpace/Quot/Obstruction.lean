/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectTensorComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FinitePresentation.FirstOrderThickening
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # The canonical obstruction to lifting a flat quotient -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The adjunction unit `F_{T'} ⟶ i_* F_T` of `fiberMap`, after identifying
`i^* F_{T'}` with `F_T`. -/
def unitToPushforward (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') :
    fiberF f F σ' ⟶
      (Modules.pushforward (fiberMap f h)).obj (fiberF f F σ) :=
  (Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app (fiberF f F σ') ≫
    (Modules.pushforward (fiberMap f h)).map (fiberFCompIso f F h).inv

/-- The domain of `Modules.action` of the ideal sheaf of `X_T ⊂ X_{T'}` on `F_{T'}`. -/
def idealTensor (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    (fiber f σ').Modules :=
  tensorObj (Hom.idealSheaf (fiberMap f h)) (fiberF f F σ')

/-- The ideal-sheaf action `I ⊗ F_{T'} ⟶ F_{T'}` on the mixed-scalar side. -/
def idealTensor_to_fiberF (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    idealTensor f F h ⟶ fiberF f F σ' :=
  Modules.action (Hom.idealSheafSubobject (fiberMap f h)) (fiberF f F σ')

/-- Tensoring the ideal comparison with the relatively flat ambient fibre module is invertible. -/
theorem isIso_tensorIdeal_comparison_fiberF (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    IsIso (tensorIdeal_comparison f h (fiberF f F σ)) :=
  sorry

/-- Pullback commutes with tensoring the ideal and the ambient fibre module. -/
theorem isIso_pullbackIdealTensorComparison (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    IsIso (Modules.DirectTensorComparison.pullbackTensor (fiberMap f h)
      (Hom.idealSheaf (fiberMap f h)) (fiberF f F σ')) :=
  sorry

/-- Comparison `i^*(I ⊗ F_{T'}) ⟶ F_T ⊗ f_T^* J` from the oplax pullback-tensor
comparison, the inverse of `fiberFCompIso`, the braiding, and the inverse of
`tensorIdeal_comparison` for `F_T`. -/
def pulledIdealTensor_to_tensorIdeal (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))] :
    (Modules.pullback (fiberMap f h)).obj (idealTensor f F h) ⟶
      tensorIdeal f h (fiberF f F σ) :=
  Modules.DirectTensorComparison.pullbackTensor (fiberMap f h)
      (Hom.idealSheaf (fiberMap f h)) (fiberF f F σ') ≫
    tensorHom (𝟙 _) (fiberFCompIso f F h).inv ≫
    (Modules.ofCommModules (fiber f σ)).map
      (β_
          ((Modules.toCommModules (fiber f σ)).obj
            ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h))))
          ((Modules.toCommModules (fiber f σ)).obj (fiberF f F σ))).hom ≫
    @inv _ _ _ _ (tensorIdeal_comparison f h (fiberF f F σ))
      tensorComparison

/-- The adjunct `I ⊗ F_{T'} ⟶ i_*(F_T ⊗ f_T^* J)` of `pulledIdealTensor_to_tensorIdeal`. -/
def idealTensor_to_pushforwardTensorIdeal (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))] :
    idealTensor f F h ⟶
      (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)) :=
  (Modules.pullbackPushforwardAdjunction (fiberMap f h)).homEquiv _ _
    (pulledIdealTensor_to_tensorIdeal f F h hF)

/-- The ideal-action domain is canonically isomorphic to the direct image of the base-ideal tensor of the relatively flat ambient module. -/
theorem isIso_idealTensor_to_pushforwardTensorIdeal (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))] :
    IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF) :=
  sorry

/-- The adjunction counit is invertible on modules on `X_T` along the thickening
`X_T ⊂ X_{T'}`. -/
theorem isIso_counit_fiberMap (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) :
    IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app G) :=
  sorry

/-- Inclusion `i_*(F_T ⊗ f_T^* J) ⟶ F_{T'}` from the braiding, `tensorIdeal_comparison`
for `F_T` only, and `Modules.action` of `Hom.idealSheafSubobject (fiberMap)` on
`F_{T'}`. -/
def unitInclusion (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] :
    (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)) ⟶
      fiberF f F σ' :=
  @inv _ _ _ _ (idealTensor_to_pushforwardTensorIdeal f F h hF)
      adjunctComparison ≫
    idealTensor_to_fiberF f F h

/-- The action inclusion vanishes after `unitToPushforward`. -/
theorem unitInclusion_comp_unitToPushforward (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] :
    unitInclusion f F h hF ≫ unitToPushforward f F h = 0 :=
  sorry

/-- The ideal-action inclusion and adjunction unit form the ambient deformation complex. -/
def unitSequence (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] : ShortComplex (fiber f σ').Modules :=
  ShortComplex.mk (unitInclusion f F h hF) (unitToPushforward f F h)
    (unitInclusion_comp_unitToPushforward f F h hF)

/-- The ambient deformation sequence is short exact for a relatively flat module. -/
theorem unitSequence_shortExact (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] :
    (unitSequence f F h hF).ShortExact := sorry

/-- The middle module and maps of the ambient deformation sequence are the fibre module,
ideal-action inclusion, and adjunction unit. -/
theorem unitSequence_spec (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] :
    (unitSequence f F h hF).X₂ = fiberF f F σ' ∧
      (unitSequence f F h hF).f = unitInclusion f F h hF ∧
      (unitSequence f F h hF).g = unitToPushforward f F h := ⟨rfl, rfl, rfl⟩

/-- Tensoring the kernel inclusion and quotient map with the base ideal gives zero composite. -/
theorem tensorKernelSequence_zero (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (Q : Point f F σ) :
    tensorIdeal_map f h (kernel.ι Q.map) ≫ tensorIdeal_map f h Q.map = 0 := sorry

/-- The kernel sequence of a quotient tensored with the pulled-back base ideal. -/
def tensorKernelSequence (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (Q : Point f F σ) : ShortComplex (fiber f σ).Modules :=
  ShortComplex.mk (tensorIdeal_map f h (kernel.ι Q.map)) (tensorIdeal_map f h Q.map)
    (tensorKernelSequence_zero f F h Q)

/-- The tensor-kernel sequence is short exact because the quotient is relatively flat. -/
theorem tensorKernelSequence_shortExact (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (Q : Point f F σ) :
    (tensorKernelSequence f F h Q).ShortExact := sorry

/-- The tensor-kernel sequence has the tensor of the ambient fibre as middle module and the
tensors of the kernel inclusion and quotient map as arrows. -/
theorem tensorKernelSequence_spec (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (Q : Point f F σ) :
    (tensorKernelSequence f F h Q).X₂ = tensorIdeal f h (fiberF f F σ) ∧
      (tensorKernelSequence f F h Q).f = tensorIdeal_map f h (kernel.ι Q.map) ∧
      (tensorKernelSequence f F h Q).g = tensorIdeal_map f h Q.map := ⟨rfl, rfl, rfl⟩

/-- The inverse image of the quotient kernel in the ambient deformation sequence. -/
def preimageSequence (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ) : ShortComplex (fiber f σ').Modules := by
  let u := (Modules.pushforward (fiberMap f h)).map (kernel.ι Q.map)
  let v := unitToPushforward f F h
  let inclusion := unitInclusion f F h hF
  let limitWitness : HasPullback u v :=
    HasLimitsOfShape.has_limit (C := (fiber f σ').Modules) _
  have condition : (0 : _ ⟶ _) ≫ u = inclusion ≫ v := by
    rw [zero_comp]
    exact (unitInclusion_comp_unitToPushforward f F h hF).symm
  exact ShortComplex.mk
    (@pullback.lift (fiber f σ').Modules _ _ _ _ _ u v limitWitness 0 inclusion condition)
    (@pullback.fst (fiber f σ').Modules _ _ _ _ u v limitWitness)
    (@pullback.lift_fst (fiber f σ').Modules _ _ _ _ _ u v limitWitness 0 inclusion condition)

/-- Pulling the ambient deformation sequence back along the kernel inclusion is short exact. -/
theorem preimageSequence_shortExact (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ) :
    (preimageSequence f F h hF Q).ShortExact := sorry

/-- Pushing the inverse-image sequence out along the tensor quotient map gives the mixed-scalar
canonical sequence. -/
def mixedCanonicalSequence (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ) : ShortComplex (fiber f σ').Modules := by
  let u := (Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h Q.map)
  let v := (preimageSequence f F h hF Q).f
  let projection := (preimageSequence f F h hF Q).g
  let colimitWitness : HasPushout u v :=
    HasColimitsOfShape.has_colimit (C := (fiber f σ').Modules) _
  have condition : u ≫ (0 : _ ⟶ _) = v ≫ projection := by
    rw [comp_zero]
    exact (preimageSequence f F h hF Q).zero.symm
  exact ShortComplex.mk
    (@pushout.inl (fiber f σ').Modules _ _ _ _ u v colimitWitness)
    (@pushout.desc (fiber f σ').Modules _ _ _ _ _ u v colimitWitness 0 projection condition)
    (@pushout.inl_desc (fiber f σ').Modules _ _ _ _ _ u v colimitWitness 0 projection condition)

/-- The mixed-scalar canonical sequence is short exact. -/
theorem mixedCanonicalSequence_shortExact (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ) :
    (mixedCanonicalSequence f F h hF Q).ShortExact := sorry

/-- The scalar-changed canonical maps have zero composite. -/
theorem canonicalSequence_zero (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ)
    [counitComparison : IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (tensorIdeal f h Q.module))] :
    (inv ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
        (tensorIdeal f h Q.module)) ≫
      (Modules.pullback (fiberMap f h)).map (mixedCanonicalSequence f F h hF Q).f) ≫
    ((Modules.pullback (fiberMap f h)).map (mixedCanonicalSequence f F h hF Q).g ≫
      (Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (kernel Q.map)) = 0 := sorry

/-- The canonical sequence of the quotient kernel by its base-ideal tensor, obtained by scalar
change and the adjunction counit from the mixed-scalar sequence. -/
def canonicalSequence (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ)
    [counitComparison : IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (tensorIdeal f h Q.module))] : ShortComplex (fiber f σ).Modules :=
  ShortComplex.mk
    (inv ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
        (tensorIdeal f h Q.module)) ≫
      (Modules.pullback (fiberMap f h)).map (mixedCanonicalSequence f F h hF Q).f)
    ((Modules.pullback (fiberMap f h)).map (mixedCanonicalSequence f F h hF Q).g ≫
      (Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (kernel Q.map))
    (canonicalSequence_zero f F h hF Q)

/-- The canonical obstruction sequence is short exact. -/
theorem canonicalSequence_shortExact (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ)
    [counitComparison : IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (tensorIdeal f h Q.module))] :
    (canonicalSequence f F h hF Q).ShortExact := sorry

/-- The canonical sequence uses pullback of the mixed-scalar middle module and counit transports on both endpoints. -/
theorem canonicalSequence_spec (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ)
    [counitComparison : IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (tensorIdeal f h Q.module))] :
    (canonicalSequence f F h hF Q).X₂ =
        (Modules.pullback (fiberMap f h)).obj
          (mixedCanonicalSequence f F h hF Q).X₂ ∧
      (canonicalSequence f F h hF Q).f =
        inv ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
            (tensorIdeal f h Q.module)) ≫
          (Modules.pullback (fiberMap f h)).map
            (mixedCanonicalSequence f F h hF Q).f ∧
      (canonicalSequence f F h hF Q).g =
        (Modules.pullback (fiberMap f h)).map
            (mixedCanonicalSequence f F h hF Q).g ≫
          (Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
            (kernel Q.map) := ⟨rfl, rfl, rfl⟩

/-- A quotient point of `F_T` lifts to `Q_{F/X/B}(T')` when it is kernel-identified with
the pullback of a quotient point of `F_{T'}`. -/
def lifts {σ σ' : SchemeOver B} (h : σ ⟶ σ') {f : X ⟶ B} {F : X.Modules}
    (x : Point f F σ) : Prop :=
  ∃ x' : Point f F σ', Rel (x'.pullback h) x

/-- Lifting along `T ⊂ T'` is existence of a kernel-identified pullback. -/
theorem lifts_iff {σ σ' : SchemeOver B} (h : σ ⟶ σ') {f : X ⟶ B} {F : X.Modules}
    (x : Point f F σ) :
    lifts h x ↔ ∃ x' : Point f F σ', Rel (x'.pullback h) x := Iff.rfl

/-- Lifts of kernel-identified quotient points correspond to the action of
`Q_{F/X/B}` on `T ⊂ T'`. -/
theorem lifts_iff_functor_map (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ) :
    lifts h x ↔
      ∃ x' : Point f F σ',
        (functor f F).map (op h)
            (Quotient.mk (quotientSetoid f F σ') x') =
          Quotient.mk (quotientSetoid f F σ) x :=
  sorry

/-- The Ext-one class of the canonical short exact sequence obstructing a flat quotient lift. -/
noncomputable def obstruction (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ) :
    Ext (kernel x.map) (tensorIdeal f h x.module) 1 :=
  (canonicalSequence_shortExact f F h hF x
    (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
    (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
    (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).extClass

/-- The obstruction class `o_x(T')` is the `Ext¹` class of the canonical short exact sequence. -/
theorem obstruction_eq (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ) :
    obstruction f F h hF x = (canonicalSequence_shortExact f F h hF x
    (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
    (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
    (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).extClass := rfl

/-- Kernel-identified quotient points determine isomorphic obstruction classes: `Rel`
supplies an isomorphism of targets from `rel_iso_iff`, hence of kernels and of
`tensorIdeal` coefficients, and the two `Ext¹` classes correspond. -/
theorem obstruction_rel (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    {x₁ x₂ : Point f F σ} (hx : Rel x₁ x₂) :
    ∃ (eQ : x₁.module ≅ x₂.module) (eK : kernel x₁.map ≅ kernel x₂.map),
      x₁.map ≫ eQ.hom = x₂.map ∧
        eK.hom ≫ kernel.ι x₂.map = kernel.ι x₁.map ∧
          obstruction f F h hF x₂ =
            (Ext.mk₀ eK.inv).precomp (tensorIdeal f h x₂.module) (zero_add 1)
              ((Ext.mk₀ (tensorIdeal_map f h eQ.hom)).postcomp (kernel x₁.map)
                (add_zero 1) (obstruction f F h hF x₁)) :=
  sorry

/-- The canonical obstruction vanishes exactly when the quotient lifts across the thickening. -/
@[stacks 0CZU]
theorem obstruction_eq_zero_iff (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ) :
    obstruction f F h hF x = 0 ↔ lifts h x :=
  sorry

/-- Every lift of a finitely presented quotient across a first-order thickening is finitely presented. -/
@[stacks 0CZU]
theorem lift_isFinitePresentation (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (x : FpPoint f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x.point) :
    x'.module.IsFinitePresentation :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
