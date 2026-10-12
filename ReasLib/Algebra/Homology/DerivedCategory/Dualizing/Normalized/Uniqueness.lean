/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Uniqueness

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- Any two normalized dualizing complexes over a Noetherian local ring are isomorphic. -/
theorem nonempty_iso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {ω ω' : DerivedCategory (ModuleCat.{u} A)}
    (hω : ω.IsNormalizedDualizingComplex H)
    (hω' : ω'.IsNormalizedDualizingComplex H) :
    Nonempty (ω ≅ ω') := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
