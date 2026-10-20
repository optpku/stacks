module

public import ReasLib.AlgebraicGeometry.Scheme.GRingStalks
import StacksCheckRecall

/-!
# Extra G-ring hypothesis for Artin contractions
-/

@[expose] public section

universe u

/- Remark 98.27.2: the Artin contraction argument requires the local rings of
the base scheme to be G-rings. The desired result for every Situation 98.27.1
remains unresolved without this assumption. -/
@[stacks 0GH9] #check
  (AlgebraicGeometry.Scheme.HasGRingStalks : AlgebraicGeometry.Scheme.{u} → Prop)

#check (AlgebraicGeometry.Scheme.HasGRingStalks.spec :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.HasGRingStalks S]
    (x : S), IsGRing (S.presheaf.stalk x))
#check (AlgebraicGeometry.Scheme.hasGRingStalks_iff_forall :
  ∀ (S : AlgebraicGeometry.Scheme.{u}),
    AlgebraicGeometry.Scheme.HasGRingStalks S ↔ ∀ x : S, IsGRing (S.presheaf.stalk x))
#check (AlgebraicGeometry.Scheme.instHasGRingStalks_of_isGRing :
  ∀ {R : Type u} [CommRing R] [IsGRing R],
    AlgebraicGeometry.Scheme.HasGRingStalks (AlgebraicGeometry.Spec (.of R)))
