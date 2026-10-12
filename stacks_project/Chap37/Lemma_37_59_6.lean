/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Restriction
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

/- Lemma 37.59.6 (1): relative `m`-pseudo-coherence is equivalent to the affine-space
pushforward criterion on every compatible pair of affine opens. -/
@[stacks 09UJ]
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.iff_affineOpens :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ),
      Scheme.ModuleDerived.IsMPseudoCoherentOver f E m ↔
        ∀ (U : X.affineOpens) (V : S.affineOpens)
          (e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
          ∃ (n : ℕ) (i : (U : X.Opens).toScheme ⟶
            AffineSpace (ULift (Fin n)) (V : S.Opens).toScheme),
            IsClosedImmersion i ∧
              i ≫ (AffineSpace (ULift (Fin n)) (V : S.Opens).toScheme ↘
                (V : S.Opens).toScheme) = f.resLE V U e ∧
              RingedSpace.ModuleDerived.IsMPseudoCoherent
                ((RingedSpace.moduleDerivedPushforward i.toShHom).obj
                  ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E)) m)

/- Lemma 37.59.6 (2): relative `m`-pseudo-coherence is preserved after restriction to
arbitrary compatible source and target opens. -/
@[stacks 09UJ]
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.restrict :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ),
      Scheme.ModuleDerived.IsMPseudoCoherentOver f E m →
        ∀ (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V),
          Scheme.ModuleDerived.IsMPseudoCoherentOver (f.resLE V U e)
            ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E) m)
