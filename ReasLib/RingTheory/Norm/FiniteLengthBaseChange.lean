module

public import ReasLib.Algebra.Module.End.FiniteLength.Pi
public import ReasLib.Algebra.Module.End.FiniteLength.BaseChange
public import ReasLib.Algebra.Module.End.FiniteLength.Norm
public import Mathlib.Algebra.Ring.NonZeroDivisors

@[expose] public section

noncomputable section

open IsLocalRing
open scoped BigOperators TensorProduct

universe u v w x y

namespace Algebra

/-- Under a flat local base change whose principal quotient decomposes into finitely many local
branches, the corresponding power of the source residue norm is the product of the branch residue
norms, weighted by the lengths of the principal quotients. -/
theorem normPow_eq_prod_ofBaseChange
    {A : Type u} {A' : Type v} {R : Type w} {i : Type x} {S : i → Type y}
    [CommRing A] [CommRing A'] [CommRing R] [∀ l, CommRing (S l)]
    [IsLocalRing A] [IsLocalRing A'] [IsLocalRing R] [∀ l, IsLocalRing (S l)]
    [Algebra A A'] [Algebra A R] [∀ l, Algebra A' (S l)]
    [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A R)]
    [∀ l, IsLocalHom (algebraMap A' (S l))] [Module.Flat A A']
    [Module.Finite (ResidueField A) (ResidueField R)]
    [∀ l, Module.Finite (ResidueField A') (ResidueField (S l))] [Fintype i]
    (π : R) (u : Rˣ) (g : ∀ l, R →+* S l) (π_nonZeroDivisor : π ∈ nonZeroDivisors R)
    (hR : IsFiniteLength R (R ⧸ Ideal.span {π}))
    (hS : ∀ l, IsFiniteLength (S l) (S l ⧸ Ideal.span {g l π}))
    (hClosedFiber : IsFiniteLength (Ideal.Fiber (maximalIdeal A) A')
      (Ideal.Fiber (maximalIdeal A) A'))
    (hg : ∀ l, (g l).comp (algebraMap A R) =
      (algebraMap A' (S l)).comp (algebraMap A A'))
    (e : A' ⊗[A] (R ⧸ Ideal.span {π}) ≃ₗ[A']
      ∀ l, S l ⧸ Ideal.span {g l π})
    (he : ∀ z l,
      e (((TensorProduct.isBaseChange A (R ⧸ Ideal.span {π}) A').endHom
        (Algebra.lsmul A A (R ⧸ Ideal.span {π}) (u : R))) z) l =
        Algebra.lsmul A' A' (S l ⧸ Ideal.span {g l π}) (g l u) (e z l)) :
    (ResidueField.map (algebraMap A A')
      (Algebra.norm (ResidueField A) (residue R u) ^
        (Module.length R (R ⧸ Ideal.span {π})).toNat)) ^
        (Module.length (Ideal.Fiber (maximalIdeal A) A')
          (Ideal.Fiber (maximalIdeal A) A')).toNat =
      ∏ l, Algebra.norm (ResidueField A') (residue (S l) (g l u)) ^
        (Module.length (S l) (S l ⧸ Ideal.span {g l π})).toNat := sorry

end Algebra

end
