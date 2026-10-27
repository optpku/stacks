/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Obstruction.Extension
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
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.tensorKernelExtension :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') (Q : Point f F σ),
    CategoryTheory.Extension (tensorIdeal f h (kernel Q.map))
      (tensorIdeal f h Q.module))

/- Remark 99.7.9 (Obstructions for quotients): preimageExtension. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.preimageExtension :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ),
    CategoryTheory.Extension
      ((Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)))
      ((Modules.pushforward (fiberMap f h)).obj (kernel Q.map)))

/- Remark 99.7.9 (Obstructions for quotients): mixedCanonicalExtension. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.mixedCanonicalExtension :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ),
    CategoryTheory.Extension
      ((Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h Q.module))
      ((Modules.pushforward (fiberMap f h)).obj (kernel Q.map)))

/- Remark 99.7.9 (Obstructions for quotients): canonicalExtension. -/
@[stacks 0CZU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.canonicalExtension :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [tensorComparison : IsIso (tensorIdeal_comparison f h (fiberF f F σ))]
    [adjunctComparison : IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF)] (Q : Point f F σ)
    [counitComparison : IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (tensorIdeal f h Q.module))]
    (hExact : (canonicalSequence f F h hF Q).ShortExact),
    CategoryTheory.Extension (tensorIdeal f h Q.module) (kernel Q.map))

end AlgebraicGeometry.AlgebraicSpace.Quot
