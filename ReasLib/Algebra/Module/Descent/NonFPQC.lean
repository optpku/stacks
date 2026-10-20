module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.TensorProduct.Equalizer

@[expose] public section

universe u

namespace Algebra

/-- There exists a commutative ring with an infinite family of flat algebras such that every
module is the equalizer of the indexed tensor-product cofaces, but no finite subfamily has
this property for every module. -/
theorem exists_infinite_flat_piTensorEqualizer_not_finite :
    ∃ (A : Type u) (_ : CommRing A) (I : Type u) (_ : Infinite I) (A_ : I → Type u)
      (_ : ∀ i, CommRing (A_ i)) (_ : ∀ i, Algebra A (A_ i)),
      (∀ i, Module.Flat A (A_ i)) ∧
        (∀ (M : Type u) [AddCommGroup M] [Module A M], Module.IsPiTensorEqualizer A A_ M) ∧
          ∀ (J : Finset I), ¬ ∀ (M : Type u) [AddCommGroup M] [Module A M],
            Module.IsPiTensorEqualizer A (fun j : J ↦ A_ (j : I)) M := sorry

end Algebra
