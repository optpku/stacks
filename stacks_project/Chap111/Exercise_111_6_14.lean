module

public import ReasLib.RingTheory.Spectrum.Prime.GenericPoint
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.14 (1): in `Spec(A)`, every irreducible closed subset has a generic point. -/
@[stacks 02D7]
#check (PrimeSpectrum.exists_isGenericPoint :
  ∀ {R : Type u} [CommSemiring R] {S : Set (PrimeSpectrum R)},
    IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x S)

/- Exercise 111.6.14 (2): the map `p ↦ closure {p}` is a bijection of `Spec(A)` with the
irreducible closed subsets of `X := Spec(A)`. -/
@[stacks 02D7]
#check (PrimeSpectrum.pointsEquivIrreducibleCloseds_bijective :
  ∀ (R : Type u) [CommSemiring R],
    Function.Bijective (PrimeSpectrum.pointsEquivIrreducibleCloseds R :
      PrimeSpectrum R → (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ))

#check (PrimeSpectrum.coe_pointsEquivIrreducibleCloseds_apply :
  ∀ {R : Type u} [CommSemiring R] (p : PrimeSpectrum R),
    ((OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds R p) :
      TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) : Set (PrimeSpectrum R)) = closure {p})

/- Companion: on a sober space the same correspondence is `irreducibleSetEquivPoints`. -/
#check @irreducibleSetEquivPoints

/- Companion: the inverse sends a point `p` to `closure {p}` as an `IrreducibleCloseds`. -/
#check @coe_irreducibleEquivPoints_symm_apply

/- Companion: on `Spec(A)` one has `closure {p} = V(p)`. -/
#check @PrimeSpectrum.closure_singleton
