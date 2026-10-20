/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.OverField.Unramified

open CategoryTheory

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Example 41.8.1 (1): An unramified quasi-compact scheme over a field is affine. -/
@[stacks 024X]
#check
  (AlgebraicGeometry.SchemeOverField.instIsAffineOfUnramifiedOfQuasiCompact :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [Unramified X.hom] [QuasiCompact X.hom], IsAffine X.left)

/- Example 41.8.1 (2): An unramified quasi-compact scheme over a field is exactly a finite
coproduct of spectra of finite separable field extensions. -/
@[stacks 024X]
#check
  (AlgebraicGeometry.SchemeOverField.unramifiedQuasiCompact_iff_exists_finiteCoproduct :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k),
      (Unramified X.hom ∧ QuasiCompact X.hom) ↔
        ∃ D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X, Finite D.ι)

/- Example 41.8.1 (3): A connected unramified scheme over a field is the spectrum of one
finite separable field extension. -/
@[stacks 024X]
#check
  (AlgebraicGeometry.SchemeOverField.exists_specFiniteSeparable_of_unramified_of_connected :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [Unramified X.hom] [ConnectedSpace X.left],
      ∃ K : CommAlgOverField k,
        IsField K ∧ FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
          Nonempty
            (Over.mk X.hom ≅
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))

/- Example 41.8.1 (4): For a scheme over a field, étale and unramified are equivalent. -/
@[stacks 024X]
#check
  (AlgebraicGeometry.SchemeOverField.etale_iff_unramified :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k),
      Etale X.hom ↔ Unramified X.hom)

end AlgebraicGeometry.SchemeOverField
