/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Affine

/-! The shared affine-site owner is re-exported for existing chapter consumers. -/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- The complete typed check keeps the affine topology available to existing
chapter consumers without retaining an item-owned implementation. -/
#check (affineTopology : ∀ S : Scheme.{u},
  GrothendieckTopology (Affine S))

end AlgebraicGeometry.Scheme.ProEt
