module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.CommSq

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- The étale precoverage is stable under base change. -/
instance etalePrecoverageIsStableUnderBaseChange :
    etalePrecoverage.IsStableUnderBaseChange := sorry

end Scheme

/-- A scheme-morphism property is étale local on source-and-target when it is stable under
étale precomposition and base change, and can be checked on pointwise étale squares. -/
class IsEtaleLocalAtSourceAndTarget (P : MorphismProperty Scheme.{u}) : Prop where
  /-- The property is preserved by precomposition with an étale morphism. -/
  respectsLeftEtale : P.RespectsLeft (@Etale : MorphismProperty Scheme.{u})
  /-- The property is preserved by base change along an étale morphism. -/
  stableUnderEtaleBaseChange :
    P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u})
  /-- The property holds exactly when it holds pointwise after passing to a commutative
  square with étale vertical morphisms. -/
  locality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔
      ∀ x : X, ∃ (U : X.Etale) (V : Y.Etale) (h : U.left ⟶ V.left) (u : U.left),
        U.hom u = x ∧ CommSq h U.hom V.hom f ∧ P h

namespace IsEtaleLocalAtSourceAndTarget

variable (P : MorphismProperty Scheme.{u})

/-- An étale-local-on-source-and-target property respects étale precomposition. -/
instance toRespectsLeftEtale [hP : IsEtaleLocalAtSourceAndTarget P] :
    P.RespectsLeft (@Etale : MorphismProperty Scheme.{u}) :=
  hP.respectsLeftEtale

/-- An étale-local-on-source-and-target property is stable under étale base change. -/
instance toStableUnderEtaleBaseChange [hP : IsEtaleLocalAtSourceAndTarget P] :
    P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u}) :=
  hP.stableUnderEtaleBaseChange

/-- The pointwise étale-square characterization of a property that is étale local on
source-and-target. -/
theorem iff_exists [IsEtaleLocalAtSourceAndTarget P] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔
      ∀ x : X, ∃ (U : X.Etale) (V : Y.Etale) (h : U.left ⟶ V.left) (u : U.left),
        U.hom u = x ∧ CommSq h U.hom V.hom f ∧ P h := sorry

/-- An étale-local-on-source-and-target property is local for étale covers of the source. -/
instance toIsLocalAtSource [IsEtaleLocalAtSourceAndTarget P] :
    P.IsLocalAtSource Scheme.etalePrecoverage := sorry

/-- An étale-local-on-source-and-target property is local for étale covers of the target. -/
instance toIsLocalAtTarget [IsEtaleLocalAtSourceAndTarget P] :
    P.IsLocalAtTarget Scheme.etalePrecoverage := sorry

/-- An étale-local-on-source-and-target property is preserved by postcomposition with an
étale morphism. -/
instance toRespectsRightEtale [IsEtaleLocalAtSourceAndTarget P] :
    P.RespectsRight (@Etale : MorphismProperty Scheme.{u}) := sorry

/-- An étale-local-on-source-and-target property descends across postcomposition with an
étale morphism. -/
instance toHasOfPostcompEtale [IsEtaleLocalAtSourceAndTarget P] :
    P.HasOfPostcompProperty (@Etale : MorphismProperty Scheme.{u}) := sorry

/-- An étale-local-on-source-and-target property holds for a morphism exactly when it holds
for the top map of every commutative square with étale vertical maps. -/
theorem iff_forall_square [IsEtaleLocalAtSourceAndTarget P] {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    P f ↔ ∀ (U : X.Etale) (V : Y.Etale) (h : U.left ⟶ V.left),
      CommSq h U.hom V.hom f → P h := sorry

/-- An étale-local-on-source-and-target property holds for a morphism exactly when it holds
for the top map of some étale square whose left vertical map is surjective. -/
theorem iff_exists_surjective_square [IsEtaleLocalAtSourceAndTarget P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∃ (U : X.Etale) (V : Y.Etale) (h : U.left ⟶ V.left),
      Surjective U.hom ∧ CommSq h U.hom V.hom f ∧ P h := sorry

/-- An étale-local-on-source-and-target property holds for a morphism exactly when it holds
after base change along every member of some étale cover of the target. -/
theorem iff_exists_targetCover [IsEtaleLocalAtSourceAndTarget P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : Y.Cover.{u} Scheme.etalePrecoverage,
      ∀ i : 𝒰.I₀, P (𝒰.pullbackHom f i) := sorry

/-- An étale-local-on-source-and-target property holds for a morphism exactly when every
member of some étale cover of the source has the property after composition with the
morphism. -/
theorem iff_exists_sourceCover [IsEtaleLocalAtSourceAndTarget P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : X.Cover.{u} Scheme.etalePrecoverage,
      ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f) := sorry

/-- An étale-local-on-source-and-target property holds for a morphism exactly when, after an
étale cover of the target, every base change has an étale source cover whose composites to
the target-cover member have the property. -/
theorem iff_exists_targetSourceCovers [IsEtaleLocalAtSourceAndTarget P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : Y.Cover.{u} Scheme.etalePrecoverage, ∀ i : 𝒰.I₀,
      ∃ 𝒱 : ((𝒰.pullback₁ f).X i).Cover.{u} Scheme.etalePrecoverage,
        ∀ j : 𝒱.I₀, P (𝒱.f j ≫ 𝒰.pullbackHom f i) := sorry

end IsEtaleLocalAtSourceAndTarget

end AlgebraicGeometry
