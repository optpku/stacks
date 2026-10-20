/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GeneratingSections.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.22.1: global generation of a quasicoherent module is preserved and reflected by a
faithfully flat affine base change. -/
@[stacks 0B57] #check (AlgebraicGeometry.Scheme.Modules.isGloballyGenerated_iff_baseChangeModule_of_faithfullyFlat :
  ∀ {A A' : Type u} [CommRing A] [CommRing A'] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    (φ : A →+* A') (hff : φ.FaithfullyFlat)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent],
    SheafOfModules.IsGloballyGenerated ℱ ↔
      SheafOfModules.IsGloballyGenerated
        (Scheme.Modules.baseChangeModule f (Spec.map (CommRingCat.ofHom φ)) ℱ))
