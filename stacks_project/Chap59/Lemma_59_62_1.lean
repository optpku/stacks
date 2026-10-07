module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Endomorphism.UniqueUpToInvertible

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

/- Lemma 59.62.1: if finite locally free positive-rank `𝒪_S`-modules `F` and `G` have
isomorphic internal endomorphism algebras, then `G` is obtained from `F` by tensoring with an
invertible module; the final equality says that this tensor isomorphism induces the given
endomorphism-algebra isomorphism. -/
@[stacks 0A2K] #check
  (AlgebraicGeometry.Scheme.Modules.exists_invertible_tensorIso_of_internalEndAlgebraIso :
    ∀ {S : Scheme.{u}} (F G : S.Modules),
      [IsFiniteLocallyFree F] → [IsFiniteLocallyFree G] →
      (hF : ∀ x : S, 0 < (fiberFinrank F x : ℕ∞)) →
      (hG : ∀ x : S, 0 < (fiberFinrank G x : ℕ∞)) →
      (h : internalHom F F ≅ internalHom G G) →
      (h_id : MonoidalClosed.id F ≫ h.hom = MonoidalClosed.id G) →
      (h_mul :
        (h.hom ⊗ₘ h.hom) ≫ MonoidalClosed.comp G G G =
          MonoidalClosed.comp F F F ≫ h.hom) →
      ∃ L : S.Modules, Invertible L ∧
        ∃ e : F ⊗ L ≅ G, h.hom = tensorEndMap F L ≫ (conjEndIso e).hom)
