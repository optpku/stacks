module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bootstrap vanishing of the cotangent complex

If `Tor^A_i(B, B) = 0` for `i > 0` and `L_{B/B ⊗[A] B} = 0`, then
`L_{B/A} = 0` in `D(B)`.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.8.3. Let `A → B` be a ring map such that `Tor^A_i(B, B) = 0` for `i > 0`
and such that `L_{B/B ⊗[A] B} = 0`. Then `L_{B/A} = 0` in `D(B)`. -/
@[stacks 08R1]
theorem derived_isZero_of_torIndependent_tensorSquare (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    (h_tor : ModuleCat.Tor.IsIndependent (ModuleCat.of A B) (ModuleCat.of A B))
    (h_zero : IsZero (DerivedCategory.Q.obj
      (RingHom.cotangentComplex (Algebra.tensorSquareMultiplication A B)))) :
    IsZero (derived A B) :=
  sorry

/-- The André-Quillen complex `Algebra.cotangentComplex A B` vanishes in `D(B)` when
`B` is Tor-independent of itself over `A` and the cotangent complex of
tensor-square multiplication vanishes. -/
theorem isZero_cotangentComplex_of_torIndependent_tensorSquare (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    (h_tor : ModuleCat.Tor.IsIndependent (ModuleCat.of A B) (ModuleCat.of A B))
    (h_zero : IsZero (DerivedCategory.Q.obj
      (RingHom.cotangentComplex (Algebra.tensorSquareMultiplication A B)))) :
    IsZero (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) :=
  sorry

end Algebra.CotangentComplex
