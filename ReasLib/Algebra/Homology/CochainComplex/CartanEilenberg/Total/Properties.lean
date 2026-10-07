module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Total

/-!
# Properties of Cartan--Eilenberg total complexes

This leaf turns the canonical termwise injectivity of a Cartan--Eilenberg total into the
typeclass facts used by derived and homotopy-category APIs.  The construction itself remains in
`CartanEilenberg.Total`; this file only owns reusable property instances.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex.Plus A}

/-- The total complex of a Cartan--Eilenberg resolution is K-injective. -/
@[stacks 015H "K-injectivity of the Cartan-Eilenberg total complex"]
instance Total.isKInjective (I : CartanEilenbergResolution K) :
    CochainComplex.IsKInjective (Total.complex I) := sorry

section Checks

variable (I : CartanEilenbergResolution K)

#synth Injective ((Total.complex I).X 0)
#synth CochainComplex.IsKInjective (Total.complex I)

end Checks

end CochainComplex.CartanEilenbergResolution
