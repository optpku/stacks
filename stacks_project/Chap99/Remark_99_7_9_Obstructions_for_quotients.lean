/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Obstruction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Deformation
import StacksCheckRecall
/-! # Remark 99.7.9 (Obstructions for quotients)

The checks retain the canonical constructions and laws. The certificates concern
the specified comparison maps and exact sequences used by inverse constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Remark 99.7.9 (Obstructions for quotients). -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.obstruction_eq_zero_iff :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ),
    obstruction f F h hF x = 0 ↔ lifts h x)

/- Remark 99.7.9 (Obstructions for quotients): instIsFirstOrderThickening_fiberMap. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.instIsFirstOrderThickening_fiberMap :
  ∀ (f : X ⟶ B) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left],
    IsFirstOrderThickening (fiberMap f h))

/- Remark 99.7.9 (Obstructions for quotients): epi_idealComparison. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.epi_idealComparison :
  ∀ (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left],
    _root_.CategoryTheory.Epi (idealComparison f h))

/- Remark 99.7.9 (Obstructions for quotients): isIso_tensorIdeal_comparison_fiberF. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isIso_tensorIdeal_comparison_fiberF :
  ∀ (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f),
    IsIso (tensorIdeal_comparison f h (fiberF f F σ)))

/- Remark 99.7.9 (Obstructions for quotients): unitSequence_shortExact. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.unitSequence_shortExact :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)],
    (unitSequence f F h hF).ShortExact)

/- Remark 99.7.9 (Obstructions for quotients): tensorKernelSequence_shortExact. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.tensorKernelSequence_shortExact :
  ∀ (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (Q : Point f F σ),
    (tensorKernelSequence f F h Q).ShortExact)

/- Remark 99.7.9 (Obstructions for quotients): unitSequence_spec. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.unitSequence_spec :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)],
    (unitSequence f F h hF).X₂ = fiberF f F σ' ∧
      (unitSequence f F h hF).f = unitInclusion f F h hF ∧
      (unitSequence f F h hF).g = unitToPushforward f F h)

/- Remark 99.7.9 (Obstructions for quotients): tensorKernelSequence_spec. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.tensorKernelSequence_spec :
  ∀ (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (Q : Point f F σ),
    (tensorKernelSequence f F h Q).X₂ = tensorIdeal f h (fiberF f F σ) ∧
      (tensorKernelSequence f F h Q).f = tensorIdeal_map f h (kernel.ι Q.map) ∧
      (tensorKernelSequence f F h Q).g = tensorIdeal_map f h Q.map)

/- Remark 99.7.9 (Obstructions for quotients): preimageSequence_shortExact. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.preimageSequence_shortExact :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ),
    (preimageSequence f F h hF Q).ShortExact)

/- Remark 99.7.9 (Obstructions for quotients): mixedCanonicalSequence_shortExact. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.mixedCanonicalSequence_shortExact :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ),
    (mixedCanonicalSequence f F h hF Q).ShortExact)

/- Remark 99.7.9 (Obstructions for quotients): canonicalSequence_spec. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.canonicalSequence_spec :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ)
    [counitComparison : IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (tensorIdeal f h Q.module))],
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
            (kernel Q.map))

/- Remark 99.7.9 (Obstructions for quotients): canonicalSequence_shortExact. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.canonicalSequence_shortExact :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ)
    [counitComparison : IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (tensorIdeal f h Q.module))],
    (canonicalSequence f F h hF Q).ShortExact)

/- Remark 99.7.9 (Obstructions for quotients): obstruction. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.obstruction :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ),
    Ext (kernel x.map) (tensorIdeal f h x.module) 1)

/- Remark 99.7.9 (Obstructions for quotients): obstruction_eq. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.obstruction_eq :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ),
    obstruction f F h hF x = (canonicalSequence_shortExact f F h hF x
    (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))
    (adjunctComparison := (isIso_idealTensor_to_pushforwardTensorIdeal f F h hF (tensorComparison := (isIso_tensorIdeal_comparison_fiberF f F h hF))))
    (counitComparison := isIso_counit_fiberMap f h (tensorIdeal f h x.module))).extClass)

/- Remark 99.7.9 (Obstructions for quotients): obstruction_rel. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.obstruction_rel :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    {x₁ x₂ : Point f F σ} (hx : Rel x₁ x₂),
    ∃ (eQ : x₁.module ≅ x₂.module) (eK : kernel x₁.map ≅ kernel x₂.map),
      x₁.map ≫ eQ.hom = x₂.map ∧
        eK.hom ≫ kernel.ι x₂.map = kernel.ι x₁.map ∧
          obstruction f F h hF x₂ =
            (Ext.mk₀ eK.inv).precomp (tensorIdeal f h x₂.module) (zero_add 1)
              ((Ext.mk₀ (tensorIdeal_map f h eQ.hom)).postcomp (kernel x₁.map)
                (add_zero 1) (obstruction f F h hF x₁)))

/- Remark 99.7.9 (Obstructions for quotients): lifts_iff_functor_map. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.lifts_iff_functor_map :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ),
    lifts h x ↔
      ∃ x' : Point f F σ',
        (functor f F).map (op h)
            (Quotient.mk (quotientSetoid f F σ') x') =
          Quotient.mk (quotientSetoid f F σ) x)

/- Remark 99.7.9 (Obstructions for quotients): lift_isFinitePresentation. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.lift_isFinitePresentation :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (x : FpPoint f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x.point),
    x'.module.IsFinitePresentation)

end AlgebraicGeometry.AlgebraicSpace.Quot
