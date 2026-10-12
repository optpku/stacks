/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteLength
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.16.4: For a normalized dualizing complex `ω` over a Noetherian local ring `A` and
an injective hull `E` of its residue field, derived internal Hom into `ω` on finite-length
`A`-modules is naturally isomorphic to ordinary dualization into `E`, concentrated in degree
zero. -/
@[stacks 0A7Q] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.finiteLengthRHomIsoMatlisDual :
    ∀ (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [AddCommGroup E] [Module A E] [Module.Injective A E]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
      (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull),
      Nonempty
        (((((Module.FiniteLengthDeterminant.moduleProperty.{u, u} A).ι ⋙
            ModuleCat.single0Functor).op) ⋙
              (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω) ≅
          ((Module.FiniteLengthDeterminant.moduleProperty.{u, u} A).ι.op ⋙
            (RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} A)).dualFunctor
              (ModuleCat.of A E) ⋙ ModuleCat.single0Functor)))
