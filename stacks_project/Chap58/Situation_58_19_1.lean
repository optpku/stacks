module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.RingTheory.LocalRing.Quotient
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (f : IsLocalRing.maximalIdeal A)

/- Situation 58.19.1: Let `A` be a Noetherian local ring with maximal ideal `𝔪`
and `f ∈ 𝔪`. Set `X = Spec(A)` and `X₀ = Spec(A ⧸ Ideal.span {(f : A)})`.
Their punctured spectra `U` and `U₀` remove the respective closed points,
corresponding to `𝔪` and its image in the quotient. Here `U` is the punctured
spectrum of `A`. -/
@[stacks 0BLF] #check (AlgebraicGeometry.PuncturedSpectrum.scheme A : AlgebraicGeometry.Scheme.{u})

/- `X` is the spectrum of `A`. -/
#check (AlgebraicGeometry.Spec (CommRingCat.of A) : AlgebraicGeometry.Scheme.{u})

/- `X₀` is the spectrum of `A/fA`. -/
#check (AlgebraicGeometry.Spec (CommRingCat.of (A ⧸ Ideal.span ({(f : A)} : Set A))) :
  AlgebraicGeometry.Scheme.{u})

/- `U₀` is the punctured spectrum of `A/fA`. -/
#check (AlgebraicGeometry.PuncturedSpectrum.scheme (A ⧸ Ideal.span ({(f : A)} : Set A)) :
  AlgebraicGeometry.Scheme.{u})

end
