/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Away.Map

/-!
# Equivalences of Principal Localizations

This leaf owns the canonical algebra equivalence obtained when a principal
localization map is bijective.  It packages the distinguished map
`Localization.awayMapₐ`, rather than a generic `AlgEquiv.ofBijective`, so
downstream code can state coefficient computations without rebuilding the
localization comparison.
-/

@[expose] public section

universe u v w

namespace Localization.Away

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra R B]

/-- Tag `051T`: a bijective canonical map of principal localizations is an algebra
equivalence. -/
@[stacks 051T "principal-localization equivalence"]
noncomputable def algEquivOfBijective (f : A →ₐ[R] B) (r : A)
    (h : Function.Bijective (Localization.awayMapₐ f r)) :
    Localization.Away r ≃ₐ[R] Localization.Away (f r) :=
  AlgEquiv.ofBijective (Localization.awayMapₐ f r) h

/-- Tag `051T`: the inverse canonical principal-localization equivalence sends the image of a
coefficient back to its source localization class. -/
@[simp, stacks 051T "principal-localization equivalence on coefficients"]
theorem algEquivOfBijective_symm_apply_algebraMap (f : A →ₐ[R] B) (r a : A)
    (h : Function.Bijective (Localization.awayMapₐ f r)) :
    (algEquivOfBijective f r h).symm
        (algebraMap B (Localization.Away (f r)) (f a)) =
      algebraMap A (Localization.Away r) a := sorry

end Localization.Away
