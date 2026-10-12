/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.AlmostBlowup
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Spec

/- Example 38.37.10: if the finitely generated ideal `J` of `A` is annihilated by a
power of `f`, then the canonical square with vertices `Spec (A ⧸ (Ideal.span {f} ⊔ J))`,
`Spec (A ⧸ J)`, `Spec (A ⧸ Ideal.span {f})`, and `Spec A` is an almost blowup square. -/
@[stacks 0EVG] #check (AlgebraicGeometry.Spec.quotientMap_isAlmostBlowupSquare :
  ∀ (A : CommRingCat.{u}) (f : A) (J : Ideal A),
    J.FG → (∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) →
      IsAlmostBlowupSquare (quotientMap J)
        (Scheme.idealSheafDataOfIdealOnSpec (Ideal.span {f})))

end Spec

end AlgebraicGeometry
