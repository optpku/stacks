/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Example_92_5_9_Simplicial
public import stacks_project.Chap92.Example_92_5_9_Terms
import Mathlib.Tactic.CrossRefAttribute

/-!
# An explicit length-two polynomial simplicial object

Example 92.5.9 constructs, from a presentation of `B` over `A`, an explicit
`2`-truncated polynomial object and the `2`-coskeleton of that object in the
slice over `B`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Algebra
open Algebra.PolynomialSite
open Algebra.Presentation.LengthTwo
open MvPolynomial
open SSet.modelCategoryQuillen

universe u

namespace Algebra.Presentation.LengthTwo

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Example 92.5.9 (1). Let `A → B` be a ring map. Choose a surjection
`P.Ring = A[u_i] ⟶ B` and generators `f_t` of `Ker(P.Ring ⟶ B)`, packaged as a
presentation `P`. This is the explicit length-two simplicial object `P_•` in
the category of `A`-algebra maps to `B`: the `2`-coskeleton of the
`2`-truncated polynomial object with carriers `term0 P = P.Ring`,
`term1 P = A[u_i, x_t]`, and `term2 P = A[u_i, y_t, z_t, v_r, w_{t,t'}]`,
and with faces `faceZero`, `faceOne`, `faceTwo` and degeneracies
`degeneracyZero`, `degeneracyOne`, following the length-two stage of
Proposition 92.5.2. -/
@[stacks 09D4]
noncomputable def resolution (P : Presentation A B ι σ) :
    SimplicialObject (Over (CommAlgCat.of A B)) :=
  (Truncated.cosk 2).obj (truncatedTwo P)

/-- Unfolding `resolution` recovers the length-two `2`-coskeleton. -/
theorem resolution_eq (P : Presentation A B ι σ) :
    resolution P = simplicial P :=
  sorry

/-- Example 92.5.9 (2). The sequence `P1 ⟶ P0 ⟶ B ⟶ 0` given by
`d0 - d1` and the presentation map is exact. -/
@[stacks 09D4]
theorem exact_faceSub (P : Presentation A B ι σ) :
    Function.Exact (fun p : term1 P ↦ faceZero P p - faceOne P p)
        (fun p : P.Ring ↦ aeval P.val p) ∧
      Function.Surjective (fun p : P.Ring ↦ aeval P.val p) :=
  sorry

/-- Example 92.5.9 (3). The joint face map `(d0, d1) : P1 ⟶ P0 ×_B P0` is
surjective. -/
@[stacks 09D4]
theorem toPullback_surjective (P : Presentation A B ι σ) {p0 p1 : P.Ring}
    (h : aeval P.val p0 = aeval P.val p1) :
    ∃ q : term1 P, faceZero P q = p0 ∧ faceOne P q = p1 :=
  sorry

/-- Example 92.5.9 (4). The augmentation of `cosk 1` of the explicit `1`-truncated
object is a trivial Kan fibration. -/
@[stacks 09D4]
theorem coskOne_trivialKan (P : Presentation A B ι σ) :
    I.rlp (underlyingSSetMap (coskOneAugmentation P)) :=
  sorry

/-- Example 92.5.9 (5). The polynomial map `P2 ⟶ cosk1(P)_2` is surjective. -/
@[stacks 09D4]
theorem toMatching_surjective (P : Presentation A B ι σ)
    {g0 g1 g2 : term1 P} (h : Triple.Compatible P g0 g1 g2) :
    ∃ q : term2 P,
      faceTwo P 0 q = g0 ∧ faceTwo P 1 q = g1 ∧ faceTwo P 2 q = g2 :=
  sorry

end Algebra.Presentation.LengthTwo
