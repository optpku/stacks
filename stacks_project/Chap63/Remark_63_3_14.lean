module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Coherence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

/- Remark 63.3.14 (1): the canonical composition isomorphisms for compact-support
direct image satisfy associativity. -/
@[stacks 0F77] #check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekCompIso_assoc :
  ∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    [IsSeparated h] [LocallyOfFiniteType h],
    etaleLowerShriekCompIso_assoc_left f g h =
      eqToHom (etaleLowerShriek_assoc f g h) ≫
        etaleLowerShriekCompIso_assoc_right f g h)

/- Remark 63.3.14 (2): the canonical composition isomorphisms for compact-support
direct image commute with base change in two vertically pasted cartesian squares. -/
@[stacks 0F77] #check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekCompIso_baseChange_vcomp :
  ∀ {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
    (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g],
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
    letI : IsSeparated f' :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_upper inferInstance
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_upper inferInstance
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
    letI : IsSeparated g' :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_lower inferInstance
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
    letI : LocallyOfFiniteType g' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_lower inferInstance
    etaleLowerShriekCompIso_baseChange_vcomp_outer f g f' g' a b c h_upper h_lower =
      etaleLowerShriekCompIso_baseChange_vcomp_inner f g f' g' a b c h_upper h_lower)
