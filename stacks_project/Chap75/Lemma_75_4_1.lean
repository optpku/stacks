module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski.Flat
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 75.4.1 (1): the morphism ε : (X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)
of 75.4.0.1 is a flat morphism of ringed sites. -/
@[stacks 08H8] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_isFlat :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      RingedSite.Hom.IsFlat.{u}
        (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski S))

/- Lemma 75.4.1 (2): the functor ε* : Mod(𝒪_X) ⟶ Mod(𝒪_étale) is exact. -/
@[stacks 08H8] #check
  (fun (X : AlgebraicGeometry.Scheme.{u}) ↦
      (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_isFlat X).exact_pullback :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      CategoryTheory.exactFunctor
        (RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite X))
        (RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Etale.Small.ringedSite X))
        (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski X).modulePullback.{u})

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- Lemma 75.4.1 (3): if ε* ℱ = 0, then ℱ = 0. -/
@[stacks 08H8]
theorem smallEtaleToZariski_modulePullback_reflects_isZero
    (X : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) :
    IsZero ((smallEtaleToZariski X).modulePullback.{u}.obj F) → IsZero F := sorry

/-- The kernel of module pullback along `smallEtaleToZariski` consists of zero objects. -/
theorem smallEtaleToZariski_modulePullback_kernel_le_isZero (X : Scheme.{u}) :
    (smallEtaleToZariski X).modulePullback.{u}.kernel ≤ IsZero := sorry

/-- A Zariski module vanishes if and only if its pullback along `smallEtaleToZariski` vanishes. -/
theorem smallEtaleToZariski_modulePullback_isZero_iff
    (X : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) :
    IsZero ((smallEtaleToZariski X).modulePullback.{u}.obj F) ↔ IsZero F := sorry

end AlgebraicGeometry.Scheme.SiteRestriction
