/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject

/-!
# Almost blowup squares of affine spectra

This file gives an almost blowup square associated to an affine quotient and a principal center.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Spec

/-- If a finitely generated ideal `J` is annihilated by a power of `f`, then the quotient map
`Spec (A ⧸ J) ⟶ Spec A` and the principal center defined by `f` determine an almost blowup
square. -/
theorem quotientMap_isAlmostBlowupSquare
    (A : CommRingCat.{u}) (f : A) (J : Ideal A)
    (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    IsAlmostBlowupSquare (quotientMap J)
      (Scheme.idealSheafDataOfIdealOnSpec (Ideal.span {f})) := sorry

end AlgebraicGeometry.Spec
