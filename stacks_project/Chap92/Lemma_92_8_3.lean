module

public import ReasLib.RingTheory.CotangentComplex.Vanishing
import StacksCheckRecall

/-!
# Bootstrap vanishing of the cotangent complex

If `Tor^A_i(B, B) = 0` for `i > 0` and `L_{B/B ⊗[A] B} = 0`, then
`L_{B/A} = 0` in `D(B)`.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 92.8.3. Let `A → B` be a ring map such that `Tor^A_i(B, B) = 0` for `i > 0`
and such that `L_{B/B ⊗[A] B} = 0`. Then `L_{B/A} = 0` in `D(B)`. -/
@[stacks 08R1] #check
  (Algebra.CotangentComplex.derived_isZero_of_torIndependent_tensorSquare :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B],
      ModuleCat.Tor.IsIndependent (ModuleCat.of A B) (ModuleCat.of A B) →
      CategoryTheory.Limits.IsZero (DerivedCategory.Q.obj
        (RingHom.cotangentComplex (Algebra.tensorSquareMultiplication A B))) →
      CategoryTheory.Limits.IsZero (Algebra.CotangentComplex.derived A B))
