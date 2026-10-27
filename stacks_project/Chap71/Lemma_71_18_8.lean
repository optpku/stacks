/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Exact
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.18.8: a quasi-coherent short complex that remains short exact after every
base change has short exact strict transform along any blowup. -/
@[stacks 0869] #check
  (AlgebraicGeometry.AlgebraicSpace.strictTransform_shortExact_of_forall_pullback_shortExact :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
      (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
      (f : X ⟶ B) (C : ShortComplex X.Modules)
      [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
      (hbase : ∀ {T : AlgebraicSpace S} (t : T ⟶ B),
        (C.map (Modules.pullback (pullback.fst f t))).ShortExact),
      (strictTransformShortComplex b (Z.inverseImageSubspace b) f C).ShortExact)

