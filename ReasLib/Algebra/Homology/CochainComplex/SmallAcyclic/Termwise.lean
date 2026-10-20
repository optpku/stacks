module

public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Bounds
public import ReasLib.Algebra.Homology.CochainComplex.Subobject.Termwise

@[expose] public section

/-!
# Constructing Small Acyclic Complexes Termwise

This module converts componentwise support, exactness, and cardinal estimates on a termwise
subcomplex into the reusable small-acyclic predicate.
-/

open CategoryTheory CategoryTheory.Limits

universe z v u

namespace CochainComplex.SmallAcyclic.BoundedBy

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {M : CochainComplex C ℤ}

/-- A termwise subcomplex with bounded-above support, degreewise exact restricted
differentials, and uniformly bounded component subobject cardinals is small and acyclic. -/
@[stacks 079K "termwise construction"]
theorem ofTermwise (S : HomologicalComplex.TermwiseSubcomplex M)
    (kappa : Cardinal.{z}) (n : ℤ)
    (hzero : ∀ i : ℤ, n < i → IsZero (S.X i))
    (hexact : ∀ i : ℤ,
      imageSubobject (S.d (i - 1) i) = kernelSubobject (S.d i (i + 1)))
    (hcard : ∀ i : ℤ,
      Cardinal.lift.{z, max u v} (Cardinal.mk (Subobject (S.X i))) ≤
        Cardinal.lift.{max u v, z} kappa) :
    CochainComplex.SmallAcyclic.BoundedBy kappa S.complex := sorry

end CochainComplex.SmallAcyclic.BoundedBy
