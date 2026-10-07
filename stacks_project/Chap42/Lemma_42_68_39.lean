module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Steinberg
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 42.68.39: the tame symbol of a one-dimensional Noetherian local domain
satisfies the Steinberg relation. -/
@[stacks 02Q9] #check (TameSymbol.value_one_sub :
  ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 1) (x y : Kˣ) (hy : (y : K) = 1 - (x : K)),
    TameSymbol.value A K hdim x y = 1)
