/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Obstruction
public import ReasLib.Algebra.Homology.ShortComplex.Splitting

/-!
# Hom-action on first-order lifts of quotient points

Along a first-order thickening `T ⊂ T'`, the group
`Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)` acts on kernel-identified lifts of a quotient
point of `F_T`. The subsheaf `K'_φ ⊂ F_{T'}` is the equalizer, inside `π⁻¹(K)`,
of `preimageToKernelRestrict` against `preimageFst ≫ i_* φ` followed by
`Q ⊗_{O_T} J ↪ ker(Q' ⟶ i_* Q)`, included into `F_{T'}` by `preimageSnd`.

The same quotient deformation construction extends to arbitrary ringed topoi once
the ideal-tensor and scalar-change comparisons for quotient kernels are available.
The splitting arithmetic is independent of the geometric setting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The group `Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)` acting on first-order lifts. -/
abbrev deformationHom (f : X ⟶ B) {F : X.Modules} {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) :=
  kernel x.map ⟶ tensorIdeal f h x.module

/-- `deformationHom` is the Hom-group from the kernel of the quotient to
`Q ⊗_{O_T} J`. -/
theorem deformationHom_eq (f : X ⟶ B) {F : X.Modules} {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) :
    deformationHom f h x = (kernel x.map ⟶ tensorIdeal f h x.module) :=
  sorry

/-- The quotient morphism of a quotient point is an epimorphism. -/
theorem epi_point_map {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    (x : Point f F σ) : Epi x.map :=
  x.map_epi

/-- Kernel inclusions of kernel-identified quotient points commute with the
subobject identification. -/
theorem relIso_kernel_comm {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {x₁ x₂ : Point f F σ} (hx : Rel x₁ x₂) :
    kernel.ι x₁.map ≫ (Iso.refl (fiberF f F σ)).hom =
      ((kernelSubobjectIso x₁.map).symm ≪≫
          Subobject.isoOfEq (kernelSubobject x₁.map) (kernelSubobject x₂.map) hx ≪≫
            kernelSubobjectIso x₂.map).hom ≫
        kernel.ι x₂.map :=
  sorry

/-- The isomorphism of targets over `F_T` supplied by kernel identification. -/
def relIso {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {x₁ x₂ : Point f F σ} (hx : Rel x₁ x₂) : x₁.module ≅ x₂.module :=
  (@asIso _ _ _ _ (Abelian.factorThruCoimage x₁.map)
      (@Abelian.isIso_factorThruCoimage _ _ _ _ _ x₁.map x₁.map_epi)).symm ≪≫
    cokernel.mapIso (kernel.ι x₁.map) (kernel.ι x₂.map)
      ((kernelSubobjectIso x₁.map).symm ≪≫
        Subobject.isoOfEq (kernelSubobject x₁.map) (kernelSubobject x₂.map) hx ≪≫
          kernelSubobjectIso x₂.map)
      (Iso.refl _) (relIso_kernel_comm hx) ≪≫
    @asIso _ _ _ _ (Abelian.factorThruCoimage x₂.map)
      (@Abelian.isIso_factorThruCoimage _ _ _ _ _ x₂.map x₂.map_epi)

/-- The isomorphism of targets commutes with the quotient maps from `F_T`. -/
theorem relIso_hom_comp {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {x₁ x₂ : Point f F σ} (hx : Rel x₁ x₂) :
    x₁.map ≫ (relIso hx).hom = x₂.map :=
  sorry

/-- The restriction `Q' ⟶ i_* Q` of a lift along `T ⊂ T'`. -/
def restrictQuotient (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    x'.module ⟶ (Modules.pushforward (fiberMap f h)).obj x.module :=
  (Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app x'.module ≫
    (Modules.pushforward (fiberMap f h)).map (relIso hx).hom

/-- `restrictQuotient` is the adjunction unit followed by `i_*` of `relIso`. -/
theorem restrictQuotient_eq (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    restrictQuotient f F h x x' hx =
      (Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app x'.module ≫
        (Modules.pushforward (fiberMap f h)).map (relIso hx).hom :=
  sorry

/-- The square comparing the quotient maps of a lift with `restrictQuotient`. -/
theorem restrictQuotient_comm (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    x'.map ≫ restrictQuotient f F h x x' hx =
      unitToPushforward f F h ≫
        (Modules.pushforward (fiberMap f h)).map x.map :=
  sorry

/-- The vanishing needed to lift `unitInclusion ≫ x'.map` through
`restrictQuotient`. -/
theorem unitInclusion_comp_restrictQuotient (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (unitInclusion f F h hF
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))) ≫ x'.map ≫ restrictQuotient f F h x x' hx = 0 :=
  sorry

/-- The map `i_*(F_T ⊗_{O_T} J) ⟶ ker(Q' ⟶ i_* Q)` from the 3×3. -/
def fiberTensorToKernelRestrict (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)) ⟶
      kernel (restrictQuotient f F h x x' hx) :=
  kernel.lift (restrictQuotient f F h x x' hx)
    ((unitInclusion f F h hF
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))) ≫ x'.map)
    (unitInclusion_comp_restrictQuotient f F h hF x x' hx)

/-- `fiberTensorToKernelRestrict` is the kernel lift of `unitInclusion ≫ x'.map`. -/
theorem fiberTensorToKernelRestrict_eq (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    fiberTensorToKernelRestrict f F h hF x x' hx =
      kernel.lift (restrictQuotient f F h x x' hx)
        ((unitInclusion f F h hF
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))) ≫ x'.map)
        (unitInclusion_comp_restrictQuotient f F h hF x x' hx) :=
  sorry

/-- The top row of the 3×3, pushed forward to `X_{T'}`.
 The specified column maps compose to zero and form a short exact sequence. -/
theorem tensorKernelPushforwardSequence_laws (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] (x : Point f F σ) :
    ∃ hz : ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map))) ≫ ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h x.map)) = 0,
      (ShortComplex.mk ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map))) ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h x.map)) hz).ShortExact := sorry

/-- The tensor-kernel short complex pushed forward along a first-order thickening. -/
def tensorKernelPushforwardSequence (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] (x : Point f F σ) :
    ShortComplex (fiber f σ').Modules where
  X₁ := (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (kernel x.map))
  X₂ := (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ))
  X₃ := (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h x.module)
  f := (Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map))
  g := (Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h x.map)
  zero := (tensorKernelPushforwardSequence_laws f F h x).choose

/-- Pushing the tensor-kernel sequence along a first-order thickening preserves short exactness. -/
theorem tensorKernelPushforwardSequence_shortExact (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] (x : Point f F σ) :
    (tensorKernelPushforwardSequence f F h x).ShortExact :=
  (tensorKernelPushforwardSequence_laws f F h x).choose_spec

/-- The vanishing of `unitInclusion ≫ x'.map` on `i_*(K ⊗ J)`. -/
theorem tensorKernel_comp_unitInclusion_map (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map)) ≫
      (unitInclusion f F h hF
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))) ≫ x'.map = 0 :=
  sorry

/-- The cokernel of `i_*(K ⊗ J ⟶ F_T ⊗ J)`, used as the honest domain of the
right-column arrow of a lift. -/
abbrev tensorIdealPushforwardCokernel (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ) : (fiber f σ').Modules :=
  cokernel
    ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map)))

/-- The right-column arrow of a lift, as `cokernel.desc` of `unitInclusion ≫ x'.map`
along `i_*(K ⊗ J ⟶ F_T ⊗ J)`. -/
def tensorIdealToQuotient (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    tensorIdealPushforwardCokernel f F h x ⟶ x'.module :=
  cokernel.desc
    ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map)))
    ((unitInclusion f F h hF
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))) ≫ x'.map)
    (tensorKernel_comp_unitInclusion_map f F h hF x x' hx)

/-- The cokernel comparison `coker(K ⊗ J ⟶ F_T ⊗ J) ⟶ Q ⊗_{O_T} J`. -/
def tensorIdealCokernelDesc (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) :
    cokernel (tensorIdeal_map f h (kernel.ι x.map)) ⟶ tensorIdeal f h x.module :=
  cokernel.desc (tensorIdeal_map f h (kernel.ι x.map))
    (tensorIdeal_map f h x.map) (tensorKernelSequence_zero f F h x)

/-- The cokernel comparison `coker(K ⊗ J ⟶ F_T ⊗ J) ⟶ Q ⊗_{O_T} J` is an
isomorphism. -/
theorem isIso_tensorIdealCokernelDesc (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ) :
    IsIso (tensorIdealCokernelDesc f F h x) :=
  sorry

/-- The cokernel of `K ⊗ J ⟶ F_T ⊗ J` identifies with `Q ⊗_{O_T} J`. -/
def tensorIdealCokernelIso (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) :
    cokernel (tensorIdeal_map f h (kernel.ι x.map)) ≅ tensorIdeal f h x.module :=
  @asIso _ _ _ _ (tensorIdealCokernelDesc f F h x) (isIso_tensorIdealCokernelDesc f F h x)

/-- The identification `coker(K ⊗ J ⟶ F_T ⊗ J) ≅ Q ⊗ J` sends the cokernel
projection to `F_T ⊗ J ⟶ Q ⊗ J`. -/
theorem tensorIdealCokernelIso_hom (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ) :
    cokernel.π (tensorIdeal_map f h (kernel.ι x.map)) ≫
      (tensorIdealCokernelIso f F h x).hom =
    tensorIdeal_map f h x.map :=
  sorry

/-- The cokernel comparison `coker(i_*(K ⊗ J ⟶ F_T ⊗ J)) ⟶ i_*(Q ⊗_{O_T} J)`. -/
def tensorIdealPushforwardCokernelDesc (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ) :
    tensorIdealPushforwardCokernel f F h x ⟶
      (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h x.module) :=
  cokernel.desc
    ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map)))
    ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h x.map))
    (by rw [← Functor.map_comp, tensorKernelSequence_zero, Functor.map_zero])

/-- The cokernel comparison `coker(i_*(K ⊗ J ⟶ F_T ⊗ J)) ⟶ i_*(Q ⊗_{O_T} J)` is
an isomorphism. -/
theorem isIso_tensorIdealPushforwardCokernelDesc (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] (x : Point f F σ) :
    IsIso (tensorIdealPushforwardCokernelDesc f F h x) :=
  sorry

/-- The cokernel of `i_*(K ⊗ J ⟶ F_T ⊗ J)` identifies with `i_*(Q ⊗_{O_T} J)`. -/
def tensorIdealPushforwardCokernelIso (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] (x : Point f F σ) :
    tensorIdealPushforwardCokernel f F h x ≅
      (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h x.module) :=
  @asIso _ _ _ _ (tensorIdealPushforwardCokernelDesc f F h x) (isIso_tensorIdealPushforwardCokernelDesc f F h x)

/-- The identification `coker(i_*(K ⊗ J ⟶ F_T ⊗ J)) ≅ i_*(Q ⊗ J)` sends the
cokernel projection to `i_*(F_T ⊗ J ⟶ Q ⊗ J)`. -/
theorem tensorIdealPushforwardCokernelIso_hom (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] (x : Point f F σ) :
    cokernel.π
        ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map))) ≫
      (tensorIdealPushforwardCokernelIso f F h x).hom =
    (Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h x.map) :=
  sorry

/-- The right column `0 ⟶ coker(i_*(K ⊗ J ⟶ F_T ⊗ J)) ⟶ Q' ⟶ i_* Q ⟶ 0` of a
lift.
 The specified column maps compose to zero and form a short exact sequence. -/
theorem quotientColumnSequence_laws (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    ∃ hz : (tensorIdealToQuotient f F h hF x x' hx) ≫ (restrictQuotient f F h x x' hx) = 0,
      (ShortComplex.mk (tensorIdealToQuotient f F h hF x x' hx) (restrictQuotient f F h x x' hx) hz).ShortExact := sorry

/-- The quotient column of a lifted flat quotient, with its canonical cokernel inclusion. -/
def quotientColumnSequence (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    ShortComplex (fiber f σ').Modules where
  X₁ := tensorIdealPushforwardCokernel f F h x
  X₂ := x'.module
  X₃ := (Modules.pushforward (fiberMap f h)).obj x.module
  f := tensorIdealToQuotient f F h hF x x' hx
  g := restrictQuotient f F h x x' hx
  zero := (quotientColumnSequence_laws f F h hF x x' hx).choose

/-- The canonical sequence from the ideal tensor quotient to a lifted quotient and its reduction is short exact. -/
theorem quotientColumnSequence_shortExact (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (quotientColumnSequence f F h hF x x' hx).ShortExact :=
  (quotientColumnSequence_laws f F h hF x x' hx).choose_spec

/-- The adjunct `F_T ⊗_{O_T} J ⟶ i^*(ker(Q' ⟶ i_* Q))` of
`fiberTensorToKernelRestrict`. -/
def fiberTensorToPullbackKernel (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    tensorIdeal f h (fiberF f F σ) ⟶
      (Modules.pullback (fiberMap f h)).obj
        (kernel (restrictQuotient f F h x x' hx)) :=
  (@asIso _ _ _ _ ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
      (tensorIdeal f h (fiberF f F σ))) (isIso_counit_fiberMap f h (tensorIdeal f h (fiberF f F σ)))).inv ≫
    (Modules.pullback (fiberMap f h)).map
      (fiberTensorToKernelRestrict f F h hF x x' hx)

/-- The vanishing of `fiberTensorToPullbackKernel` on `K ⊗_{O_T} J`. -/
theorem tensorKernel_comp_fiberTensorToPullbackKernel (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    tensorIdeal_map f h (kernel.ι x.map) ≫
        fiberTensorToPullbackKernel f F h hF x x' hx = 0 :=
  sorry

/-- The comparison `coker(K ⊗ J ⟶ F_T ⊗ J) ⟶ i^*(ker(Q' ⟶ i_* Q))` of the
right column, as `cokernel.desc` of `fiberTensorToPullbackKernel`. -/
def tensorIdealToPullbackKernel (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    cokernel (tensorIdeal_map f h (kernel.ι x.map)) ⟶
      (Modules.pullback (fiberMap f h)).obj
        (kernel (restrictQuotient f F h x x' hx)) :=
  cokernel.desc (tensorIdeal_map f h (kernel.ι x.map))
    (fiberTensorToPullbackKernel f F h hF x x' hx)
    (tensorKernel_comp_fiberTensorToPullbackKernel f F h hF x x' hx)

/-- The kernel of a lift maps into `i_* F_T` with vanishing composite along `i_* x.map`. -/
theorem kernelRestrict_comp (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (kernel.ι x'.map ≫ unitToPushforward f F h) ≫
        (Modules.pushforward (fiberMap f h)).map x.map = 0 :=
  sorry

/-- The restriction `K' ⟶ ker(i_* (F_T ⟶ Q))` of the kernel of a lift. -/
def kernelRestrict (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    kernel x'.map ⟶
      kernel ((Modules.pushforward (fiberMap f h)).map x.map) :=
  kernel.lift ((Modules.pushforward (fiberMap f h)).map x.map)
    (kernel.ι x'.map ≫ unitToPushforward f F h) (kernelRestrict_comp f F h x x' hx)

/-- The vanishing of `i_*(K ⊗ J) ⟶ F_{T'} ⟶ Q'` needed to define `K ⊗ J ⟶ K'`. -/
theorem kernelRestrictArrow_comp (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map)) ≫
      (unitInclusion f F h hF
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF)))))) ≫ x'.map = 0 :=
  sorry

/-- The left vertical arrow `i_*(K ⊗ J) ⟶ K'` of the 3×3 diagram of a lift. -/
def kernelRestrictArrow (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (kernel x.map)) ⟶
      kernel x'.map :=
  kernel.lift x'.map
    ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map)) ≫
      (unitInclusion f F h hF
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))))
    (kernelRestrictArrow_comp f F h hF x x' hx)

/-- The vanishing of `i^*(K' ⟶ i_* F_T)` after `x.map`. -/
theorem pullbackKernel_comp_map (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    ((Modules.pullback (fiberMap f h)).map
        (kernel.ι x'.map ≫ unitToPushforward f F h) ≫
      (Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
        (fiberF f F σ)) ≫ x.map = 0 :=
  sorry

/-- The left-column projection `i^* K' ⟶ K` of a lift. -/
def pullbackKernelRestrict (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (Modules.pullback (fiberMap f h)).obj (kernel x'.map) ⟶ kernel x.map :=
  kernel.lift x.map
    ((Modules.pullback (fiberMap f h)).map
        (kernel.ι x'.map ≫ unitToPushforward f F h) ≫
      (Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
        (fiberF f F σ))
    (pullbackKernel_comp_map f F h x x' hx)

/-- The left-column projection `K' ⟶ i_* K` of a lift. -/
def kernelToPushforwardKernel (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    kernel x'.map ⟶
      (Modules.pushforward (fiberMap f h)).obj (kernel x.map) :=
  (Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app (kernel x'.map) ≫
    (Modules.pushforward (fiberMap f h)).map
      (pullbackKernelRestrict f F h x x' hx)

/-- The left column `0 ⟶ i_*(K ⊗ J) ⟶ K' ⟶ i_* K ⟶ 0` of a lift.
 The specified column maps compose to zero and form a short exact sequence. -/
theorem kernelColumnSequence_laws (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    ∃ hz : (kernelRestrictArrow f F h hF x x' hx) ≫ (kernelToPushforwardKernel f F h x x' hx) = 0,
      (ShortComplex.mk (kernelRestrictArrow f F h hF x x' hx) (kernelToPushforwardKernel f F h x x' hx) hz).ShortExact := sorry

/-- The kernel column of a lifted flat quotient. -/
def kernelColumnSequence (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    ShortComplex (fiber f σ').Modules where
  X₁ := (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (kernel x.map))
  X₂ := kernel x'.map
  X₃ := (Modules.pushforward (fiberMap f h)).obj (kernel x.map)
  f := kernelRestrictArrow f F h hF x x' hx
  g := kernelToPushforwardKernel f F h x x' hx
  zero := (kernelColumnSequence_laws f F h hF x x' hx).choose

/-- The canonical sequence from the ideal tensor kernel to a lifted kernel and its reduction is short exact. -/
theorem kernelColumnSequence_shortExact (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (kernelColumnSequence f F h hF x x' hx).ShortExact :=
  (kernelColumnSequence_laws f F h hF x x' hx).choose_spec

/-- The preimage `π⁻¹(K) ⊂ F_{T'}` is the middle object of `preimageSequence`. -/
abbrev preimageModule (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) : (fiber f σ').Modules :=
  (preimageSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))).X₂

/-- The first projection of `π⁻¹(K)` lands in `i_* K`. -/
abbrev preimageFst (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) :
    preimageModule f F h hF x ⟶
      (Modules.pushforward (fiberMap f h)).obj (kernel x.map) :=
  @Limits.pullback.fst (fiber f σ').Modules _ _ _ _
    ((Modules.pushforward (fiberMap f h)).map (kernel.ι x.map))
    (unitToPushforward f F h)
    (HasLimitsOfShape.has_limit (C := (fiber f σ').Modules) _)

/-- The second projection of `π⁻¹(K)` lands in `F_{T'}`. -/
abbrev preimageSnd (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) :
    preimageModule f F h hF x ⟶ fiberF f F σ' :=
  @Limits.pullback.snd (fiber f σ').Modules _ _ _ _
    ((Modules.pushforward (fiberMap f h)).map (kernel.ι x.map))
    (unitToPushforward f F h)
    (HasLimitsOfShape.has_limit (C := (fiber f σ').Modules) _)

/-- Compatibility of `kernelToPushforwardKernel` with the pullback defining `π⁻¹(K)`. -/
theorem kernelToPreimage_condition (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    kernelToPushforwardKernel f F h x x' hx ≫
        (Modules.pushforward (fiberMap f h)).map (kernel.ι x.map) =
      kernel.ι x'.map ≫ unitToPushforward f F h :=
  sorry

/-- The map `K' ⟶ π⁻¹(K)` of a lift. -/
def kernelToPreimage (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    kernel x'.map ⟶ preimageModule f F h hF x :=
  @Limits.pullback.lift (fiber f σ').Modules _ _ _ _ _
    ((Modules.pushforward (fiberMap f h)).map (kernel.ι x.map))
    (unitToPushforward f F h)
    (HasLimitsOfShape.has_limit (C := (fiber f σ').Modules) _)
    (kernelToPushforwardKernel f F h x x' hx)
    (kernel.ι x'.map)
    (kernelToPreimage_condition f F h hF x x' hx)

/-- The map `K' ⟶ mixedCanonicalSequence.X₂` of a lift. -/
def kernelToMixed (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    kernel x'.map ⟶ (mixedCanonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))).X₂ :=
  kernelToPreimage f F h hF x x' hx ≫
    Limits.pushout.inr
      ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h x.map))
      (preimageSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))).f

/-- `K ⊗ J` is killed in `mixedCanonicalSequence.X₂` along a lift. -/
theorem kernelRestrictArrow_comp_kernelToMixed (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    kernelRestrictArrow f F h hF x x' hx ≫ kernelToMixed f F h hF x x' hx = 0 :=
  sorry

/-- A section of `mixedCanonicalSequence.X₂` extracted from a lift, as
`cokernel.desc` of `kernelToMixed` along `kernelRestrictArrow`. -/
def mixedSplittingSection (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    cokernel (kernelRestrictArrow f F h hF x x' hx) ⟶
      (mixedCanonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))).X₂ :=
  cokernel.desc (kernelRestrictArrow f F h hF x x' hx)
    (kernelToMixed f F h hF x x' hx)
    (kernelRestrictArrow_comp_kernelToMixed f F h hF x x' hx)

/-- The vanishing of `preimageSnd ≫ x'.map` after `restrictQuotient`. -/
theorem preimageSnd_comp_restrictQuotient (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    preimageSnd f F h hF x ≫ x'.map ≫ restrictQuotient f F h x x' hx = 0 :=
  sorry

/-- The map `π⁻¹(K) ⟶ ker(Q' ⟶ i_* Q)` recording the image in `Q'`. -/
def preimageToKernelRestrict (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    preimageModule f F h hF x ⟶ kernel (restrictQuotient f F h x x' hx) :=
  kernel.lift (restrictQuotient f F h x x' hx)
    (preimageSnd f F h hF x ≫ x'.map)
    (preimageSnd_comp_restrictQuotient f F h hF x x' hx)

/-- The vanishing of `i_*(K ⊗ J ⟶ F_T ⊗ J)` on `fiberTensorToKernelRestrict`. -/
theorem tensorKernel_comp_fiberTensorToKernelRestrict (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map)) ≫
      fiberTensorToKernelRestrict f F h hF x x' hx = 0 :=
  sorry

/-- The comparison `coker(i_*(K ⊗ J ⟶ F_T ⊗ J)) ⟶ ker(Q' ⟶ i_* Q)`. -/
def tensorIdealPushforwardCokernelToKernelRestrict (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    tensorIdealPushforwardCokernel f F h x ⟶
      kernel (restrictQuotient f F h x x' hx) :=
  cokernel.desc
    ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h (kernel.ι x.map)))
    (fiberTensorToKernelRestrict f F h hF x x' hx)
    (tensorKernel_comp_fiberTensorToKernelRestrict f F h hF x x' hx)

/-- The inclusion `i_*(Q ⊗_{O_T} J) ↪ ker(Q' ⟶ i_* Q)` of the right column. -/
def tensorIdealToKernelRestrict (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h x.module) ⟶
      kernel (restrictQuotient f F h x x' hx) :=
  (tensorIdealPushforwardCokernelIso f F h x).inv ≫
    tensorIdealPushforwardCokernelToKernelRestrict f F h hF x x' hx

/-- The inclusion `i_*(Q ⊗_{O_T} J) ↪ ker(Q' ⟶ i_* Q)` recovers
`fiberTensorToKernelRestrict` after `i_*(F_T ⊗ J ⟶ Q ⊗ J)`. -/
theorem tensorIdealToKernelRestrict_comp (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h x.map) ≫
      tensorIdealToKernelRestrict f F h hF x x' hx =
    fiberTensorToKernelRestrict f F h hF x x' hx :=
  sorry

/-- The comparison `π⁻¹(K) ⟶ ker(Q' ⟶ i_* Q)` sending a local section with
image `k` in `K` to `φ(k)`. -/
def preimageToHomKernelRestrict (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) :
    preimageModule f F h hF x ⟶ kernel (restrictQuotient f F h x x' hx) :=
  preimageFst f F h hF x ≫
    (Modules.pushforward (fiberMap f h)).map φ ≫
      tensorIdealToKernelRestrict f F h hF x x' hx

/-- `preimageToHomKernelRestrict` is `preimageFst ≫ i_* φ` followed by
`Q ⊗_{O_T} J ↪ ker(Q' ⟶ i_* Q)`. -/
theorem preimageToHomKernelRestrict_eq (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) :
    preimageToHomKernelRestrict f F h hF x x' hx φ =
      preimageFst f F h hF x ≫
        (Modules.pushforward (fiberMap f h)).map φ ≫
          tensorIdealToKernelRestrict f F h hF x x' hx :=
  sorry

/-- The subsheaf `K'_φ ⊂ F_{T'}` as the equalizer, inside `π⁻¹(K)`, of the image
in `Q'` against `φ(k) ∈ Q ⊗_{O_T} J ⊂ Q'`. -/
def kernelOfHom (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) :
    (fiber f σ').Modules :=
  equalizer
    (preimageToKernelRestrict f F h hF x x' hx)
    (preimageToHomKernelRestrict f F h hF x x' hx φ)

/-- The inclusion `K'_φ ⟶ F_{T'}`, as the equalizer inclusion into `π⁻¹(K)`
followed by `preimageSnd`. -/
def kernelOfHom_arrow (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) :
    kernelOfHom f F h hF x x' hx φ ⟶ fiberF f F σ' :=
  equalizer.ι
      (preimageToKernelRestrict f F h hF x x' hx)
      (preimageToHomKernelRestrict f F h hF x x' hx φ) ≫
    preimageSnd f F h hF x

/-- The inclusion `K'_φ ⟶ F_{T'}` is a monomorphism. -/
theorem mono_kernelOfHom_arrow (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) :
    Mono (kernelOfHom_arrow f F h hF x x' hx φ) :=
  sorry

/-- Membership in `K'_φ ⊂ F_{T'}` is the local-section condition: a morphism
`s` factors through `kernelOfHom_arrow` iff its image in `F_T` is a section `k`
of `K` and its image in `Q'` is the section `φ(k)` of `Q ⊗_{O_T} J`. -/
theorem mem_kernelOfHom (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x)
    {U : (fiber f σ').Modules} (s : U ⟶ fiberF f F σ') :
    (∃ t : U ⟶ kernelOfHom f F h hF x x' hx φ,
        t ≫ kernelOfHom_arrow f F h hF x x' hx φ = s) ↔
      ∃ k : U ⟶ (Modules.pushforward (fiberMap f h)).obj (kernel x.map),
        s ≫ unitToPushforward f F h =
            k ≫ (Modules.pushforward (fiberMap f h)).map (kernel.ι x.map) ∧
          s ≫ x'.map =
            k ≫ (Modules.pushforward (fiberMap f h)).map φ ≫
              tensorIdealToKernelRestrict f F h hF x x' hx ≫
                kernel.ι (restrictQuotient f F h x x' hx) :=
  sorry

/-- The quotient `Q'_φ = F_{T'}/K'_φ` associated to `φ`.
 The quotient by the equalizer subsheaf is quasi-coherent and relatively flat. -/
theorem pointOfHom_properties (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) :
    (cokernel (@Subobject.mk _ _ _ _ (kernelOfHom_arrow f F h hF x x' hx φ)
        (mono_kernelOfHom_arrow f F h hF x x' hx φ)).arrow).IsQuasicoherent ∧
      Modules.flatOver (cokernel (@Subobject.mk _ _ _ _ (kernelOfHom_arrow f F h hF x x' hx φ)
        (mono_kernelOfHom_arrow f F h hF x x' hx φ)).arrow) (pullback.snd f σ'.hom) := sorry

/-- The quotient of the ambient fibre by the equalizer-defined subsheaf associated to a homomorphism. -/
def pointOfHom (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) : Point f F σ' :=
  Point.ofKernel f F σ' (@Subobject.mk _ _ _ _ (kernelOfHom_arrow f F h hF x x' hx φ)
        (mono_kernelOfHom_arrow f F h hF x x' hx φ)) (pointOfHom_properties f F h hF x x' hx φ).1 (pointOfHom_properties f F h hF x x' hx φ).2

/-- `pointOfHom` is the cokernel of `K'_φ ⊂ F_{T'}`. -/
theorem pointOfHom_spec (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) :
    (pointOfHom f F h hF x x' hx φ).module =
        cokernel (@Subobject.mk _ _ _ _ (kernelOfHom_arrow f F h hF x x' hx φ)
        (mono_kernelOfHom_arrow f F h hF x x' hx φ)).arrow ∧
      (pointOfHom f F h hF x x' hx φ).map =
        cokernel.π (@Subobject.mk _ _ _ _ (kernelOfHom_arrow f F h hF x x' hx φ)
        (mono_kernelOfHom_arrow f F h hF x x' hx φ)).arrow :=
  sorry

/-- The constructed quotient `Q'_φ` pulls back to the original quotient point. -/
theorem pointOfHom_rel (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) :
    Rel ((pointOfHom f F h hF x x' hx φ).pullback h) x :=
  sorry

/-- A kernel-identified lift of a quotient point `x` along `T ⊂ T'`. -/
structure Lift (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ) where
  /-- The kernel-identified quotient class on `T'`. -/
  val : (functor f F).obj (op σ')
  /-- The class pulls back to `x` along `T ⊂ T'`. -/
  map_eq :
    (functor f F).map (op h) val = Quotient.mk (quotientSetoid f F σ) x

namespace Lift

/-- Assemble a lift from a quotient point of `F_{T'}` kernel-identified with `x`.
 The class of a lifted quotient restricts to the original quotient class. -/
theorem mkPoint_map_eq (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ)
    (x' : Point f F σ') (hx : Rel (x'.pullback h) x) :
    (functor f F).map (op h) (Quotient.mk (quotientSetoid f F σ') x') = Quotient.mk (quotientSetoid f F σ) x := sorry

/-- The quotient-class lift determined by a kernel-identified quotient point. -/
def mkPoint (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ)
    (x' : Point f F σ') (hx : Rel (x'.pullback h) x) : Lift f F h x where
  val := Quotient.mk (quotientSetoid f F σ') x'
  map_eq := mkPoint_map_eq f F h x x' hx

/-- The lift `Q'_φ` associated to a homomorphism `φ` and a base lift. -/
def ofHom (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x) : Lift f F h x :=
  mkPoint f F h x (pointOfHom f F h hF x x' hx φ)
    (pointOfHom_rel f F h hF x x' hx φ)

/-- A representative of a lift class restricts to a kernel-identified quotient. -/
theorem representative_rel (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ)
    (L : Lift f F h x) : Rel ((Quotient.out L.val).pullback h) x := sorry

/-- Translate a lift by a homomorphism `φ : K ⟶ Q ⊗_{O_T} J`.
Translation uses the quotient by the modified equalizer kernel. -/
def vadd (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (φ : deformationHom f h x) (L : Lift f F h x) : Lift f F h x :=
  ofHom f F h hF x (Quotient.out L.val) (representative_rel f F h x L) φ

/-- The kernel of a second lift maps into the kernel of `Q' ⟶ i_* Q` of a first lift.
 The comparison between two lifted kernels vanishes after quotient restriction. -/
theorem vsubToKernel_zero (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (x : Point f F σ)
    (x₁ x₂ : Point f F σ') (hx₁ : Rel (x₁.pullback h) x)
    (hx₂ : Rel (x₂.pullback h) x) :
    (kernel.ι x₁.map ≫ x₂.map) ≫ restrictQuotient f F h x x₂ hx₂ = 0 := sorry

/-- The canonical map from one lifted kernel to the restriction kernel of a second quotient. -/
def vsubToKernel (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (x : Point f F σ)
    (x₁ x₂ : Point f F σ') (hx₁ : Rel (x₁.pullback h) x)
    (hx₂ : Rel (x₂.pullback h) x) :
    kernel x₁.map ⟶ kernel (restrictQuotient f F h x x₂ hx₂) :=
  kernel.lift (restrictQuotient f F h x x₂ hx₂) (kernel.ι x₁.map ≫ x₂.map) (vsubToKernel_zero f F h hF x x₁ x₂ hx₁ hx₂)

end Lift

/-- The left-column cokernel comparison `coker(i_*(K ⊗ J) ⟶ K') ⟶ i_* K`, as
`cokernel.desc` of `kernelToPushforwardKernel`.
 The kernel column maps compose to zero. -/
theorem kernelColumnCokernelToPushforward_zero (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    kernelRestrictArrow f F h hF x x' hx ≫ kernelToPushforwardKernel f F h x x' hx = 0 := sorry

/-- The canonical cokernel comparison from a lifted kernel to the pushed-forward original kernel. -/
def kernelColumnCokernelToPushforward (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    cokernel (kernelRestrictArrow f F h hF x x' hx) ⟶
      (Modules.pushforward (fiberMap f h)).obj (kernel x.map) :=
  cokernel.desc (kernelRestrictArrow f F h hF x x' hx)
    (kernelToPushforwardKernel f F h x x' hx) (kernelColumnCokernelToPushforward_zero f F h hF x x' hx)

/-- The left-column comparison `coker(i_*(K ⊗ J) ⟶ K') ⟶ i_* K` is an
isomorphism. -/
theorem isIso_kernelColumnCokernelToPushforward (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    IsIso (kernelColumnCokernelToPushforward f F h hF x x' hx) :=
  sorry

/-- The cokernel of `i_*(K ⊗ J) ⟶ K'` identifies with `i_* K`. -/
def kernelColumnCokernelIso (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    cokernel (kernelRestrictArrow f F h hF x x' hx) ≅
      (Modules.pushforward (fiberMap f h)).obj (kernel x.map) :=
  @asIso _ _ _ _ (kernelColumnCokernelToPushforward f F h hF x x' hx) (isIso_kernelColumnCokernelToPushforward f F h hF x x' hx)

/-- The comparison `i_* K ⟶ mixedCanonicalSequence.X₂` of a lift, obtained by
inverting the left-column cokernel iso and composing with
`mixedSplittingSection`. -/
def kernelPushforwardToMixed (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (Modules.pushforward (fiberMap f h)).obj (kernel x.map) ⟶
      (mixedCanonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))).X₂ :=
  (kernelColumnCokernelIso f F h hF x x' hx).inv ≫
    mixedSplittingSection f F h hF x x' hx

/-- A section of `canonicalSequence.g` extracted from a chosen lift, as the
adjunct of `kernelPushforwardToMixed` along the counit isomorphism. -/
def splittingSection (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    kernel x.map ⟶ (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).X₂ :=
  (@asIso _ _ _ _ ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
      (kernel x.map)) (isIso_counit_fiberMap f h (kernel x.map))).inv ≫
    (Modules.pullback (fiberMap f h)).map
      (kernelPushforwardToMixed f F h hF x x' hx)

/-- A splitting of `canonicalSequence` extracted from a chosen lift of `x`.
 The complementary projection determined by a lift has image in the extension kernel. -/
theorem splittingOfLift_zero (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (𝟙 _ - (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).g ≫ splittingSection f F h hF x x' hx) ≫ (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).g = 0 := sorry

/-- The retraction and section extracted from a lift satisfy the splitting identities. -/
theorem splittingOfLift_laws (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).f ≫ (@ShortComplex.Exact.lift _ _ _ _ _ (canonicalSequence_shortExact f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).exact _
    (𝟙 _ -
      (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).g ≫ splittingSection f F h hF x x' hx)
    (splittingOfLift_zero f F h hF x x' hx) (canonicalSequence_shortExact f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).mono_f) = 𝟙 _ ∧
    (splittingSection f F h hF x x' hx) ≫ (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).g = 𝟙 _ ∧
    (@ShortComplex.Exact.lift _ _ _ _ _ (canonicalSequence_shortExact f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).exact _
    (𝟙 _ -
      (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).g ≫ splittingSection f F h hF x x' hx)
    (splittingOfLift_zero f F h hF x x' hx) (canonicalSequence_shortExact f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).mono_f) ≫ (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).f + (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).g ≫ (splittingSection f F h hF x x' hx) = 𝟙 _ := sorry

/-- The extension splitting extracted from a lifted quotient using the specified comparison inverses. -/
def splittingOfLift (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).Splitting where
  r := @ShortComplex.Exact.lift _ _ _ _ _ (canonicalSequence_shortExact f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).exact _
    (𝟙 _ -
      (canonicalSequence f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).g ≫ splittingSection f F h hF x x' hx)
    (splittingOfLift_zero f F h hF x x' hx) (canonicalSequence_shortExact f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).mono_f
  s := splittingSection f F h hF x x' hx
  f_r := (splittingOfLift_laws f F h hF x x' hx).1
  s_g := (splittingOfLift_laws f F h hF x x' hx).2.1
  id := (splittingOfLift_laws f F h hF x x' hx).2.2

/-- Subtract two kernel-identified lifts, as a homomorphism `K ⟶ Q ⊗_{O_T} J`.
The difference is obtained from the splittings of the canonical obstruction sequence. -/
def Lift.vsub (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)

    (L₁ L₂ : Lift f F h x) : deformationHom f h x :=
  ShortComplex.Splitting.vsub (canonicalSequence_shortExact f F h hF x
      (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
      (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
      (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module)))
    (splittingOfLift f F h hF x (Quotient.out L₁.val) (Lift.representative_rel f F h x L₁))
    (splittingOfLift f F h hF x (Quotient.out L₂.val) (Lift.representative_rel f F h x L₂))

/-- The difference `L₁ -ᵥ L₂` is the unique `φ` whose associated functor class
`Q'_φ` equals `L₁` relative to `L₂`. -/
theorem Lift.vsub_spec (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)



    (L₁ L₂ : Lift f F h x) (φ : deformationHom f h x) :
    Lift.vsub f F h hF x L₁ L₂ = φ ↔
      L₁ = Lift.vadd f F h hF x φ L₂ :=
  sorry

/-- Assume `F`
is flat over `B` and `T ⊂ T'` is a first-order thickening of schemes over `B`.
If `o_x(T') = 0`, then the set of kernel-identified lifts `x' ∈ Q_{F/X/B}(T')`
is a principal homogeneous space under `Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)`. -/
@[stacks 0CZV]
theorem lifts_addTorsor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ)
    (hobs : obstruction f F h hF x = 0) :
    ∃ t : AddTorsor (deformationHom f h x) (Lift f F h x),
      t.toVAdd.vadd = Lift.vadd f F h hF x ∧
        t.toVSub.vsub = Lift.vsub f F h hF x :=
  sorry

/-- Given a lift of `x` to `Q_{F/X/B}(T')`, the assignment `φ ↦ Q'_φ` is a
bijection between `Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)` and the set of
kernel-identified lifts of `x`. -/
theorem pointOfHom_bijective (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    Function.Bijective (fun φ : deformationHom f h x ↦
      Lift.ofHom f F h hF x x' hx φ) :=
  sorry

/-- The Hom-group `Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)` acts simply transitively on
the nonempty type of kernel-identified lifts. The flatness witness is an explicit parameter.
 Translation and difference of quotient lifts satisfy the torsor identities. -/
theorem addTorsorLift_laws (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)



    [Nonempty (Lift f F h x)] :
    (∀ L, Lift.vadd f F h hF x 0 L = L) ∧
    (∀ φ ψ L, Lift.vadd f F h hF x (φ + ψ) L = Lift.vadd f F h hF x φ (Lift.vadd f F h hF x ψ L)) ∧
    (∀ L M, Lift.vadd f F h hF x (Lift.vsub f F h hF x L M) M = L) ∧
    (∀ φ L, Lift.vsub f F h hF x (Lift.vadd f F h hF x φ L) L = φ) := sorry

/-- The torsor of quotient lifts with its concrete translation and difference operations. -/
@[reducible] def addTorsorLift (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)



    [Nonempty (Lift f F h x)] :
    AddTorsor (deformationHom f h x) (Lift f F h x) where
  vadd := Lift.vadd f F h hF x
  vsub := Lift.vsub f F h hF x
  zero_vadd := (addTorsorLift_laws f F h hF x).1
  add_vadd := (addTorsorLift_laws f F h hF x).2.1
  vsub_vadd' := (addTorsorLift_laws f F h hF x).2.2.1
  vadd_vsub' := (addTorsorLift_laws f F h hF x).2.2.2

end AlgebraicGeometry.AlgebraicSpace.Quot
