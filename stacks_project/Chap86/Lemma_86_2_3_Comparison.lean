module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import stacks_project.Chap75.Lemma_75_4_2_Pullback
public import stacks_project.Chap75.Lemma_75_4_2_SmallEtale

/-!
# Étale affine comparison for derived internal Hom

This file constructs the composite `ε^* ∘ tilde` from `D(A)` to `D(𝒪_étale)` on
`Spec(A)` and the canonical comparison from `ε^*` of affine `RHom` to the derived
internal Hom of the pulled-back complexes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalClosed
open Functor.PullbackInternalHom.Left
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.SiteRestriction
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

/-- The exact derived functor `ε^* ∘ tilde` from `D(A)` to derived modules on the
small étale site of `Spec(A)`. -/
noncomputable abbrev affineEtaleTildeDerived (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory
        (RingedSite.ModuleCat.{u}
          (Scheme.Etale.Small.ringedSite (Spec (CommRingCat.of A)))) :=
  affineTildeDerived A ⋙
    schemeToZariskiDerived (Spec (CommRingCat.of A)) ⋙
      (IsFlat.exactPullback
        (smallEtaleToZariski (Spec (CommRingCat.of A)))).mapDerivedCategory

/-- `affineEtaleTildeDerived` is the composite of affine tilde, the Zariski comparison,
and exact pullback along `smallEtaleToZariski`. -/
theorem affineEtaleTildeDerived_eq (A : Type u) [CommRing A] :
    affineEtaleTildeDerived A =
      affineTildeDerived A ⋙
        schemeToZariskiDerived (Spec (CommRingCat.of A)) ⋙
          (IsFlat.exactPullback
            (smallEtaleToZariski (Spec (CommRingCat.of A)))).mapDerivedCategory :=
  sorry

/-- Objectwise, `affineEtaleTildeDerived` applies affine tilde, then the Zariski
comparison, then exact étale pullback. -/
theorem affineEtaleTildeDerived_obj (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (affineEtaleTildeDerived A).obj K =
      ((IsFlat.exactPullback
          (smallEtaleToZariski (Spec (CommRingCat.of A)))).mapDerivedCategory).obj
        ((schemeToZariskiDerived (Spec (CommRingCat.of A))).obj
          ((affineTildeDerived A).obj K)) :=
  sorry

/-- The canonical comparison from `ε^* tilde RHom_A(K, L)` to the derived internal Hom
of `ε^* tilde K` and `ε^* tilde L` on the small étale site of `Spec(A)`. -/
noncomputable def etaleAffineComparison {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [MonoidalCategory
      (DerivedCategory
        (RingedSite.ModuleCat.{u}
          (Scheme.Etale.Small.ringedSite (Spec (CommRingCat.of A)))))]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed
      (DerivedCategory
        (RingedSite.ModuleCat.{u}
          (Scheme.Etale.Small.ringedSite (Spec (CommRingCat.of A))))))
    (T : Functor.TensorComparison (affineEtaleTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (affineEtaleTildeDerived A).obj (RHom.obj K L) ⟶
      (ihomOf H ((affineEtaleTildeDerived A).obj K)).obj
        ((affineEtaleTildeDerived A).obj L) :=
  (affineEtaleTildeDerived A).map (M.objIso K L).hom ≫
    comparisonApp M.closed H (affineEtaleTildeDerived A) T K L

/-- `etaleAffineComparison` is the image of the RHom identification followed by the
pullback/internal-Hom comparison of `affineEtaleTildeDerived`. -/
theorem etaleAffineComparison_eq {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [MonoidalCategory
      (DerivedCategory
        (RingedSite.ModuleCat.{u}
          (Scheme.Etale.Small.ringedSite (Spec (CommRingCat.of A)))))]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed
      (DerivedCategory
        (RingedSite.ModuleCat.{u}
          (Scheme.Etale.Small.ringedSite (Spec (CommRingCat.of A))))))
    (T : Functor.TensorComparison (affineEtaleTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    etaleAffineComparison M H T K L =
      (affineEtaleTildeDerived A).map (M.objIso K L).hom ≫
        comparisonApp M.closed H (affineEtaleTildeDerived A) T K L :=
  sorry

/-- Over a Noetherian commutative ring, the étale affine-tilde comparison for derived
internal Hom is an isomorphism when the source has finite homology in every degree and
the target has finite injective dimension. -/
theorem etaleAffineComparison_isIso {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [MonoidalCategory
      (DerivedCategory
        (RingedSite.ModuleCat.{u}
          (Scheme.Etale.Small.ringedSite (Spec (CommRingCat.of A)))))]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed
      (DerivedCategory
        (RingedSite.ModuleCat.{u}
          (Scheme.Etale.Small.ringedSite (Spec (CommRingCat.of A))))))
    (T : Functor.TensorComparison (affineEtaleTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hL : L.HasFiniteInjectiveDimension) :
    IsIso (etaleAffineComparison M H T K L) :=
  sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

