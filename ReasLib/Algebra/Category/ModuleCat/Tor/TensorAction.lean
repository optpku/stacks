/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tor
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Tensor-Product Algebra Action on `Tor`

@stack 08HW

For commutative `R`-algebras `A` and `B`, functoriality of `Tor` in its two
arguments gives commuting actions of `A` and `B` on `Tor_n^R(A, B)`.  This
leaf combines them into the canonical `A ⊗[R] B`-module used by flat
base-change statements.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Tor.TensorAction

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- The underlying `R`-module of `Tor_n^R(A, B)`. -/
abbrev underlying (n : ℕ) : ModuleCat R :=
  ((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R A)).obj (ModuleCat.of R B)

/-- Multiplication by `a : A` on the first argument induces an endomorphism of
`Tor_n^R(A, B)`. -/
noncomputable def leftScalar (n : ℕ) (a : A) :
    Module.End R (underlying (R := R) (A := A) (B := B) n) :=
  (((CategoryTheory.Tor (ModuleCat R) n).map
    (ModuleCat.ofHom ((Algebra.lmul R A) a))).app (ModuleCat.of R B)).hom

/-- The first-variable scalar action preserves zero. -/
theorem leftScalar_zero (n : ℕ) :
    leftScalar (R := R) (A := A) (B := B) n 0 = 0 := sorry

/-- The first-variable scalar action preserves one. -/
theorem leftScalar_one (n : ℕ) :
    leftScalar (R := R) (A := A) (B := B) n 1 = 1 := sorry

/-- The first-variable scalar action preserves addition. -/
theorem leftScalar_add (n : ℕ) (a b : A) :
    leftScalar (R := R) (A := A) (B := B) n (a + b) =
      leftScalar n a + leftScalar n b := sorry

/-- The first-variable scalar action preserves multiplication. -/
theorem leftScalar_mul (n : ℕ) (a b : A) :
    leftScalar (R := R) (A := A) (B := B) n (a * b) =
      leftScalar n a * leftScalar n b := sorry

/-- The first-variable action restricts to the original `R`-module action. -/
theorem leftScalar_algebraMap (n : ℕ) (r : R) :
    leftScalar (R := R) (A := A) (B := B) n ((algebraMap R A) r) =
      (algebraMap R (Module.End R (underlying (R := R) (A := A) (B := B) n))) r := sorry

/-- The algebra action on `Tor_n^R(A, B)` induced from its first argument. -/
noncomputable def leftAction (n : ℕ) :
    A →ₐ[R] Module.End R (underlying (R := R) (A := A) (B := B) n) where
  toFun := leftScalar (R := R) (A := A) (B := B) n
  map_zero' := leftScalar_zero n
  map_one' := leftScalar_one n
  map_add' := leftScalar_add n
  map_mul' := leftScalar_mul n
  commutes' := leftScalar_algebraMap n

/-- Multiplication by `b : B` on the second argument induces an endomorphism
of `Tor_n^R(A, B)`. -/
noncomputable def rightScalar (n : ℕ) (b : B) :
    Module.End R (underlying (R := R) (A := A) (B := B) n) :=
  (((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R A)).map
    (ModuleCat.ofHom ((Algebra.lmul R B) b))).hom

/-- The second-variable scalar action preserves zero. -/
theorem rightScalar_zero (n : ℕ) :
    rightScalar (R := R) (A := A) (B := B) n 0 = 0 := sorry

/-- The second-variable scalar action preserves one. -/
theorem rightScalar_one (n : ℕ) :
    rightScalar (R := R) (A := A) (B := B) n 1 = 1 := sorry

/-- The second-variable scalar action preserves addition. -/
theorem rightScalar_add (n : ℕ) (a b : B) :
    rightScalar (R := R) (A := A) (B := B) n (a + b) =
      rightScalar n a + rightScalar n b := sorry

/-- The second-variable scalar action preserves multiplication. -/
theorem rightScalar_mul (n : ℕ) (a b : B) :
    rightScalar (R := R) (A := A) (B := B) n (a * b) =
      rightScalar n a * rightScalar n b := sorry

/-- The second-variable action restricts to the original `R`-module action. -/
theorem rightScalar_algebraMap (n : ℕ) (r : R) :
    rightScalar (R := R) (A := A) (B := B) n ((algebraMap R B) r) =
      (algebraMap R (Module.End R (underlying (R := R) (A := A) (B := B) n))) r := sorry

/-- The algebra action on `Tor_n^R(A, B)` induced from its second argument. -/
noncomputable def rightAction (n : ℕ) :
    B →ₐ[R] Module.End R (underlying (R := R) (A := A) (B := B) n) where
  toFun := rightScalar (R := R) (A := A) (B := B) n
  map_zero' := rightScalar_zero n
  map_one' := rightScalar_one n
  map_add' := rightScalar_add n
  map_mul' := rightScalar_mul n
  commutes' := rightScalar_algebraMap n

/-- The two functorial scalar actions on `Tor_n^R(A, B)` commute. -/
theorem leftAction_commute_rightAction (n : ℕ) (a : A) (b : B) :
    Commute ((leftAction (R := R) (A := A) (B := B) n) a)
      ((rightAction (R := R) (A := A) (B := B) n) b) := sorry

/-- The canonical `A ⊗[R] B`-action on `Tor_n^R(A, B)`. -/
@[stacks 08HW "tensor-product algebra action on Tor"]
noncomputable def tensorAction (n : ℕ) :
    A ⊗[R] B →ₐ[R] Module.End R (underlying (R := R) (A := A) (B := B) n) :=
  Algebra.TensorProduct.lift
    (leftAction (R := R) (A := A) (B := B) n)
    (rightAction (R := R) (A := A) (B := B) n)
    (leftAction_commute_rightAction (R := R) (A := A) (B := B) n)

/-- On a pure tensor, the tensor-product action is the composite of the two
argument actions. -/
@[stacks 08HW "pure-tensor action on Tor"]
theorem tensorAction_tmul (n : ℕ) (a : A) (b : B) :
    tensorAction (R := R) (A := A) (B := B) n (a ⊗ₜ[R] b) =
      leftScalar n a * rightScalar n b := sorry

/-- The module structure obtained from the canonical tensor-product action. -/
noncomputable abbrev module (n : ℕ) :
    Module (A ⊗[R] B) (underlying (R := R) (A := A) (B := B) n) :=
  Module.compHom _ (tensorAction (R := R) (A := A) (B := B) n).toRingHom

/-- `Tor_n^R(A, B)` bundled as a module over `A ⊗[R] B`. -/
@[stacks 08HW "Tor as a tensor-product algebra module"]
noncomputable abbrev obj (n : ℕ) : ModuleCat (A ⊗[R] B) :=
  letI : Module (A ⊗[R] B) (underlying (R := R) (A := A) (B := B) n) :=
    module (R := R) (A := A) (B := B) n
  ModuleCat.of (A ⊗[R] B) (underlying (R := R) (A := A) (B := B) n)

end CategoryTheory.ModuleCat.Tor.TensorAction
