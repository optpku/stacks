module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.AffineSpace.StandardZariskiCover
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
  (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ)

/-- Relative `m`-pseudo-coherence is equivalent to the affine-space pushforward criterion
on every compatible pair of affine opens. -/
@[stacks 09UJ]
theorem iff_affineOpens :
    IsMPseudoCoherentOver f E m ↔
      ∀ (U : X.affineOpens) (V : S.affineOpens)
        (e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
        ∃ (n : ℕ) (i : (U : X.Opens).toScheme ⟶
          AffineSpace (ULift (Fin n)) (V : S.Opens).toScheme),
          IsClosedImmersion i ∧
            i ≫ (AffineSpace (ULift (Fin n)) (V : S.Opens).toScheme ↘
              (V : S.Opens).toScheme) = f.resLE V U e ∧
            RingedSpace.ModuleDerived.IsMPseudoCoherent
              ((RingedSpace.moduleDerivedPushforward i.toShHom).obj
                ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E)) m := sorry

/-- Relative `m`-pseudo-coherence is preserved after restriction to arbitrary compatible
source and target opens. -/
@[stacks 09UJ]
theorem restrict (hE : IsMPseudoCoherentOver f E m) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) :
    IsMPseudoCoherentOver (f.resLE V U e)
      ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E) m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
