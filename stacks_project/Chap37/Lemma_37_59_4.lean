module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.AffineSpace.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace RingedSpace
namespace ModuleDerived
namespace IsMPseudoCoherent

/- Lemma 37.59.4: the affine-space pushforward criterion for an object on a finite-type
affine scheme over a standard open of `S` passes to its restriction to any affine open,
viewed over `S`. -/
@[stacks 09VD] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.exists_affineSpace_pushforward_restrict :
    ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (r : Γ(S, ⊤))
    (f : X ⟶ (S.basicOpen r).toScheme) [Scheme.Hom.FiniteType f]
    (U : X.affineOpens) (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ)
    (hE : ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (S.basicOpen r).toScheme),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace (ULift.{u} (Fin n)) (S.basicOpen r).toScheme ↘
          (S.basicOpen r).toScheme) = f ∧
        IsMPseudoCoherent ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m),
    ∃ (n : ℕ) (i : (U : X.Opens).toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) =
          (U : X.Opens).ι ≫ f ≫ (S.basicOpen r).ι ∧
        IsMPseudoCoherent
          ((RingedSpace.moduleDerivedPushforward i.toShHom).obj
            ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace
              (U : X.Opens)).obj E)) m)

end IsMPseudoCoherent
end ModuleDerived
end RingedSpace
end AlgebraicGeometry
