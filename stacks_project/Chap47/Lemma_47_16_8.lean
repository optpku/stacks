/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.ZeroDimensional
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.16.8: over a zero-dimensional Noetherian local ring, a normalized
dualizing complex is isomorphic to an injective hull of the residue field concentrated
in degree zero. -/
@[stacks 0A7R] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.isoSingleInjectiveHull_of_ringKrullDim_eq_zero :
    ∀ (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [AddCommGroup E] [Module A E] [Module.Injective A E]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
      (hdim : ringKrullDim A = 0)
      (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull),
      Nonempty (ω ≅ ModuleCat.single0 (ModuleCat.of A E)))
