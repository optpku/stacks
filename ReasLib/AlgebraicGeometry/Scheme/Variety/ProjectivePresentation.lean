/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

/-!
# Projective-space presentations of varieties

This leaf relates projective and quasi-projective varieties to presentations
in finite-dimensional projective space over the base field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k]

/-- A variety over `k` is projective exactly when its structure morphism is `HProjective`, namely
when it has a closed-immersion presentation into a projective space over `Spec k`. -/
theorem projectiveVariety_iff_hProjective (X : SchemeOverField k) [Variety X] :
    ProjectiveVariety X ↔ HProjective X.hom := sorry

/-- A variety over `k` is quasi-projective exactly when its structure morphism is
`HQuasiProjective`, namely when it has a quasi-compact locally closed immersion presentation into
a projective space over `Spec k`. -/
theorem quasiProjectiveVariety_iff_hQuasiProjective (X : SchemeOverField k) [Variety X] :
    QuasiProjectiveVariety X ↔ HQuasiProjective X.hom := sorry

end

end AlgebraicGeometry
