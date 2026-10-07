module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.ExactPairing
import StacksCheckRecall

/-!
# Lemma 15.127.3

@stack 0FNS

The source equivalence and its canonical-dual identification are owned by ReasLib.
-/

@[expose] public section

/- Lemma 15.127.3 (0FNS), equivalence of (1) and (2): an object of `D(R)` admits an exact
pairing if and only if it is perfect. -/
@[stacks 0FNS "equivalence of (1) and (2)"]
#check @CategoryTheory.DerivedCategory.exists_exactPairing_iff_isPerfect

/- The canonical object-property view of the exact-pairing condition. -/
#check @CategoryTheory.DerivedCategory.isLeftDualizable_iff_isPerfect

/- Lemma 15.127.3 (0FNS), canonical dual: a chosen left dual is canonically isomorphic
to `RHom(M, R[0])`. -/
@[stacks 0FNS "canonical left dual"]
#check @CategoryTheory.DerivedCategory.Perfect.Duality.leftDualIso
