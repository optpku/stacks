module

public import ReasLib.Algebra.Category.ModuleCat.Descent.Pushforward

/-!
# Faithfully flat descent for module categories

The scalar-extension comparison along a faithfully flat ring homomorphism is
an equivalence whose inverse is the descent pushforward functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Comonad.ComonadicityInternal

namespace ModuleCat

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The scalar-extension comparison along a faithfully flat ring homomorphism,
with the equalizer-valued descent pushforward as inverse. -/
noncomputable def faithfullyFlatDescentEquivalence (f : R →+* S)
    (hf : f.FaithfullyFlat) :
    ModuleCat.{u} R ≌ (extendRestrictScalarsAdj.{u} f).toComonad.Coalgebra := by
  -- Local instance justification (proof-local temporary data): Mathlib's comparisonAdjunction.toEquivalence consumes the canonical IsEquivalence witness derived from hf only while constructing this returned equivalence.
  letI : (Comonad.comparison (extendRestrictScalarsAdj.{u} f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  exact (comparisonAdjunction (extendRestrictScalarsAdj.{u} f)).toEquivalence

/-- The forward functor of faithfully flat descent is the canonical comonad
comparison induced by scalar extension. -/
theorem faithfullyFlatDescentEquivalence_functor (f : R →+* S)
    (hf : f.FaithfullyFlat) :
    (faithfullyFlatDescentEquivalence f hf).functor =
      Comonad.comparison (extendRestrictScalarsAdj.{u} f) := rfl

/-- The inverse functor of faithfully flat descent is descent pushforward. -/
theorem faithfullyFlatDescentEquivalence_inverse (f : R →+* S)
    (hf : f.FaithfullyFlat) :
    (faithfullyFlatDescentEquivalence f hf).inverse =
      descentPushforward.{u, u, u} f := rfl

end ModuleCat
