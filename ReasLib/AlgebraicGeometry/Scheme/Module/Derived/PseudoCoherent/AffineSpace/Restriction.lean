module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.AffineSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace RingedSpace
namespace ModuleDerived
namespace IsMPseudoCoherent

/-- The affine-space pushforward criterion for a complex on an affine scheme over a
standard open is preserved by restriction to an affine open, viewed over the base. -/
@[stacks 09VD]
theorem exists_affineSpace_pushforward_restrict
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (r : Γ(S, ⊤))
    (f : X ⟶ (S.basicOpen r).toScheme) [Scheme.Hom.FiniteType f]
    (U : X.affineOpens) (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ)
    (hE : ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (S.basicOpen r).toScheme),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace (ULift.{u} (Fin n)) (S.basicOpen r).toScheme ↘
          (S.basicOpen r).toScheme) = f ∧
        IsMPseudoCoherent ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m) :
    ∃ (n : ℕ) (i : (U : X.Opens).toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) =
          (U : X.Opens).ι ≫ f ≫ (S.basicOpen r).ι ∧
        IsMPseudoCoherent
          ((RingedSpace.moduleDerivedPushforward i.toShHom).obj
            ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace
              (U : X.Opens)).obj E)) m := sorry

end IsMPseudoCoherent
end ModuleDerived
end RingedSpace
end AlgebraicGeometry
