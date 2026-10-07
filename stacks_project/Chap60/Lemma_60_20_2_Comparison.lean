module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.PolynomialPoincare

@[expose] public section

universe u

namespace DPPolynomial.DeRham

/- The source-facing names are owned by the reusable divided-power calculus API. -/
#check (formB : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {J : Ideal B}, DividedPowers J → Type u)
#check (formP : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {J : Ideal B}, DividedPowers J → Type u → Type u)
#check (derivationB : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {J : Ideal B}, (δ : DividedPowers J) → Derivation A B (formB A B δ))

end DPPolynomial.DeRham

end
