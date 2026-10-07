module

public import stacks_project.Chap86.Lemma_86_2_3_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalClosed
open Functor.PullbackInternalHom.Left
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Scheme.ModuleDerived.InternalHom
open Scheme.Etale.Small

noncomputable section

universe u

/- Lemma 86.2.3: let A be a Noetherian ring and X = Spec(A). Let 𝒪_étale be the
structure sheaf of X on the small étale site of X. Let K, L be objects of D(A).
If K ∈ D_Coh(A) and L has finite injective dimension, then
ε^* tilde RHom_A(K, L) = RSheafHom_{𝒪_étale}(ε^* tilde K, ε^* tilde L)
in D(𝒪_étale), where ε : (X_étale, 𝒪_étale) ⟶ (X, 𝒪_X) is the morphism of
ringed sites from Derived Categories of Spaces, Section 75.4, encoded as
schemeToZariskiDerived followed by exact pullback along smallEtaleToZariski. -/
@[stacks 0E50]
#check
  (etaleAffineComparison_isIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [@RHom.Has.{u, u} A _]
      [MonoidalCategory
        (DerivedCategory (RingedSite.ModuleCat.{u} (ringedSite (Spec (CommRingCat.of A)))))]
      (M : @RHom.BifunctorComparison A _ _ _)
      (H : MonoidalClosed
        (DerivedCategory (RingedSite.ModuleCat.{u} (ringedSite (Spec (CommRingCat.of A))))))
      (T : Functor.TensorComparison (affineEtaleTildeDerived A))
      (K L : DerivedCategory (ModuleCat.{u} A)),
      (∀ i : ℤ,
        Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) →
      DerivedCategory.HasFiniteInjectiveDimension L →
      IsIso (etaleAffineComparison M H T K L))
