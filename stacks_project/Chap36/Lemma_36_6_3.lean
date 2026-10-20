/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Coproduct
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
variable (hT : IsRetrocompact ((T : Set X)ᶜ)) (I : Type u)

/- Lemma 36.6.3: if `X \ T` is retrocompact, the closed-support coreflector preserves
arbitrary direct sums in `D_QCoh(𝒪_X)`. -/
@[stacks 0G7H] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.coreflector.preservesCoproducts
    X T hT I : PreservesColimitsOfShape (Discrete I) (SupportedOn.coreflector X T hT))

end AlgebraicGeometry.Scheme.DerivedQCoh
