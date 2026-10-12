/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_3_4_Length
import StacksCheckRecall

/-!
# Degree of a field over the image of a finite ring map

For a ring map `Λ → k` to a field, write `k'` for the image of `Λ` in `k`.
Then `[k : k'] = [k : residueImage Λ k]`, and this degree is finite when
`k` is finite as a `Λ`-module.
-/

@[expose] public section

open Algebra

universe u v

namespace Algebra

/-- 90.3.3.1 (1): the degree of `k` over the image subalgebra `(Algebra.ofId Λ k).range`
equals the degree of `k` over `residueImage Λ k = Λ ⧸ ker(algebraMap Λ k)`. -/
@[stacks 06S2]
theorem finrank_range_eq_finrank_residueImage {Λ : Type u} {k : Type v}
    [CommRing Λ] [Field k] [Algebra Λ k] :
    Module.finrank (Algebra.ofId Λ k).range k =
      Module.finrank (residueImage Λ k) k :=
  sorry

section
variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

/- 90.3.3.1 (2): the same degree is finite: `Module.Finite (residueImage Λ k) k`
when `k` is finite over `Λ`, already owned by `Algebra.residueImage.instFinite`. -/
@[stacks 06S2] #check residueImage.instFinite

end

end Algebra
