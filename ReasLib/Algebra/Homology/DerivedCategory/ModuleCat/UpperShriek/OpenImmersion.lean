/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange.Perfect

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory
namespace ModuleCat
namespace UpperShriek
namespace Presentation

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- If a ring homomorphism from a Noetherian ring induces an open immersion on spectra,
its presentation-defined upper-shriek functor is isomorphic to derived extension of scalars. -/
theorem isomorphicDerivedExtensionOfIsOpenImmersion [IsNoetherianRing R]
    (φ : R →+* R') (p : Presentation φ)
    [AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))] :
    IsIsomorphic p.functor (ModuleCat.derivedExtensionOfScalars φ) := sorry

/-- Upper shriek along a principal localization of a Noetherian ring is isomorphic to
derived extension of scalars along the localization map. -/
theorem isomorphicDerivedExtensionOfLocalizationAway [IsNoetherianRing R]
    (f : R) (p : Presentation (algebraMap R (Localization.Away f))) :
    IsIsomorphic p.functor
      (ModuleCat.derivedExtensionOfScalars (algebraMap R (Localization.Away f))) := sorry

end Presentation
end UpperShriek
end ModuleCat
end CategoryTheory
