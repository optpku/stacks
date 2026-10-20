module

public import ReasLib.RingTheory.Sequence.Koszul.DerivedFactorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# A transition factorization through a powered Koszul tensor product

Lemma 23.12.4 concerns the ground-ring tensor product `K_n ⊗_R K_t`, regarded in the derived
category of left differential graded `K_N`-modules.  It asks for a map from `K_t` into this tensor
product whose composite with multiplication is the relevant transition map.  Thus the categorical
shape is a factorization of the transition morphism, not a section of multiplication and not a
relative derived tensor product over `K_N`.

The exact-power Koszul algebras, their transitions, the direct and iterated restricted left-module
structures, the ground-ring tensor action, and multiplication are explicit reusable data.  Their
images in the derived category give the source statement directly, while the canonical monoidal
comparison identifies the multiplication with extension of `KoszulComplex.powTensorMul`.
-/

/- Lemma 23.12.4 (Tag 0GZ7): a sufficiently late powered Koszul transition factors through the
ground-ring tensor `K_n ⊗[R] K_t` in the derived category of left DG `K_N`-modules. -/
universe u

section

variable {R : Type u} [CommRing R]
variable {ι : Type u} [Finite ι]
variable (f : ι → R) {t n : ℕ}
variable (h_t : 1 ≤ t) (h_tn : t ≤ n)

@[stacks 0GZ7 "derived factorization through a powered Koszul ground tensor"]
#check (KoszulComplex.Derived.existsFactorization f h_t h_tn :
  ∃ (N : ℕ) (hN : n < N)
    (α : KoszulComplex.Derived.stage f (h_tn.trans hN.le) ⟶
      KoszulComplex.Derived.tensor f t hN.le),
    α ≫ KoszulComplex.Derived.multiplication f h_tn hN.le =
      KoszulComplex.Derived.transition f h_tn hN.le)

end
#check @KoszulComplex.Derived.Factorization
#check @KoszulComplex.Derived.nonemptyFactorization

#check @KoszulComplex.Derived.powDGA
#check @KoszulComplex.Derived.powDGAHom
#check @KoszulComplex.Derived.stage
#check @KoszulComplex.Derived.restrictedStage
#check @KoszulComplex.Derived.tensor
#check @KoszulComplex.Derived.tensorDGA
#check @KoszulComplex.Derived.transition
#check @KoszulComplex.Derived.multiplication
#check @KoszulComplex.Derived.multiplicationMap
#check @KoszulComplex.Derived.tensorDGAIso
#check @KoszulComplex.Derived.multiplicationMap_eq
#check @KoszulComplex.powTensorMul
