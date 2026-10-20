module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.FieldProperty
public import ReasLib.RingTheory.RingHom.Fiber.Local

@[expose] public section

/-!
# Local criteria for properties of fibers

@stack 0BK8

A local field-algebra property can be tested on fiber algebras, on all prime-local fiber rings,
or only on maximal-local fiber rings.
-/

universe u

namespace FieldAlgebraProperty

/-- For a ring map with Noetherian target, a local field-algebra property on every fiber is
equivalent to its prime-local and maximal-local formulations. -/
@[stacks 0BK8 "local criterion for fiber properties"]
theorem fiber_tfae (P : FieldAlgebraProperty.{u, u}) [P.IsLocal]
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A] :
    ([ ∀ p : PrimeSpectrum R, P p.asIdeal.ResidueField (p.asIdeal.Fiber A)
      , ∀ q : PrimeSpectrum A,
          P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R A q)
      , ∀ m : MaximalSpectrum A,
          P (m.toPrimeSpectrum.asIdeal.under R).ResidueField
            (fiberLocalRingAt R A m.toPrimeSpectrum)
      ] : List Prop).TFAE := sorry

end FieldAlgebraProperty
