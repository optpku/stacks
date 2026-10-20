/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.SyntomicLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace UniversalFiniteFreeAlgebra

/- Remark 49.11.6 (1) -/
@[stacks 0FL3]
#check (UniversalFiniteFreeAlgebra.syntomicLocusFamilySmooth :
  (d : ℕ+) → (U_d : (baseScheme d).Opens) →
    (∀ {X : Scheme.{0}} (f : X ⟶ baseScheme d),
      (∃ g : X ⟶ U_d.toScheme, g ≫ U_d.ι = f) ↔
        Syntomic (pullback.snd (projection d) f)) →
      Smooth ((projection d ∣_ U_d) ≫ U_d.ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (CoefficientRing d)))))

/- Remark 49.11.6 (2) -/
@[stacks 0FL3]
#check (UniversalFiniteFreeAlgebra.syntomicLocusProjection_not_smooth :
  (d : ℕ+) → (U_d : (baseScheme d).Opens) →
    (∀ {X : Scheme.{0}} (f : X ⟶ baseScheme d),
      (∃ g : X ⟶ U_d.toScheme, g ≫ U_d.ι = f) ↔
        Syntomic (pullback.snd (projection d) f)) →
    (2 ≤ d) → ¬ Smooth (projection d ∣_ U_d))

end UniversalFiniteFreeAlgebra
