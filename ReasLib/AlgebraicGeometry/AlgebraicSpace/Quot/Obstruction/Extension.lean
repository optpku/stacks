/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Obstruction
public import ReasLib.CategoryTheory.Abelian.Extension.Basic

/-! # Fixed-endpoint presentations of the quotient obstruction sequences -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The kernel sequence tensored with the base ideal. -/
def tensorKernelExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (Q : Point f F σ) :
    CategoryTheory.Extension (tensorIdeal f h (kernel Q.map))
      (tensorIdeal f h Q.module) where
  E := (tensorKernelSequence f F h Q).X₂
  f := (tensorKernelSequence f F h Q).f
  g := (tensorKernelSequence f F h Q).g
  zero := (tensorKernelSequence f F h Q).zero
  shortExact := tensorKernelSequence_shortExact f F h Q

/-- The inverse-image extension of the quotient kernel. -/
def preimageExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ) :
    CategoryTheory.Extension
      ((Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)))
      ((Modules.pushforward (fiberMap f h)).obj (kernel Q.map)) where
  E := (preimageSequence f F h hF Q).X₂
  f := (preimageSequence f F h hF Q).f
  g := (preimageSequence f F h hF Q).g
  zero := (preimageSequence f F h hF Q).zero
  shortExact := preimageSequence_shortExact f F h hF Q

/-- The mixed-scalar extension obtained by pushout along the tensor quotient. -/
def mixedCanonicalExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ) :
    CategoryTheory.Extension
      ((Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h Q.module))
      ((Modules.pushforward (fiberMap f h)).obj (kernel Q.map)) where
  E := (mixedCanonicalSequence f F h hF Q).X₂
  f := (mixedCanonicalSequence f F h hF Q).f
  g := (mixedCanonicalSequence f F h hF Q).g
  zero := (mixedCanonicalSequence f F h hF Q).zero
  shortExact := mixedCanonicalSequence_shortExact f F h hF Q

/-- The canonical extension after scalar change to the closed fibre, storing
the supplied exactness certificate for computational extraction of splittings. -/
def canonicalExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ)
    [counitComparison : IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (tensorIdeal f h Q.module))]
    (hExact : (canonicalSequence f F h hF Q).ShortExact) :
    CategoryTheory.Extension (tensorIdeal f h Q.module) (kernel Q.map) where
  E := (canonicalSequence f F h hF Q).X₂
  f := (canonicalSequence f F h hF Q).f
  g := (canonicalSequence f F h hF Q).g
  zero := (canonicalSequence f F h hF Q).zero
  shortExact := hExact

end AlgebraicGeometry.AlgebraicSpace.Quot
