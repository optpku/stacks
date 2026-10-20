/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber

/-!
# Unramified schemes over a field

This file describes unramified schemes over a field in terms of finite
coproducts of spectra of finite separable field extensions.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- An unramified quasi-compact scheme over a field is exactly a finite
coproduct of spectra of finite separable field extensions. -/
theorem unramifiedQuasiCompact_iff_exists_finiteCoproduct {k : Type u} [Field k]
    (X : SchemeOverField k) :
    (Unramified X.hom ∧ QuasiCompact X.hom) ↔
      ∃ D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X, Finite D.ι := sorry

/-- An unramified quasi-compact scheme over a field is affine. -/
instance instIsAffineOfUnramifiedOfQuasiCompact {k : Type u} [Field k]
    (X : SchemeOverField k) [Unramified X.hom] [QuasiCompact X.hom] :
    IsAffine X.left := sorry

/-- A connected unramified scheme over a field is the spectrum of a finite
separable field extension. -/
theorem exists_specFiniteSeparable_of_unramified_of_connected {k : Type u} [Field k]
    (X : SchemeOverField k) [Unramified X.hom] [ConnectedSpace X.left] :
    ∃ K : CommAlgOverField k,
      IsField K ∧ FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
        Nonempty
          (Over.mk X.hom ≅
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := sorry

/-- A scheme over a field is étale if and only if it is unramified. -/
theorem etale_iff_unramified {k : Type u} [Field k] (X : SchemeOverField k) :
    Etale X.hom ↔ Unramified X.hom := sorry

end AlgebraicGeometry.SchemeOverField
