module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace MorphismProperty

/- Lemma 67.27.4 (1): A base change of a quasi-finite morphism is quasi-finite. -/
@[stacks 03XL] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiFinite_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, IsStableUnderBaseChange
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 67.27.4 (2): A base change of a locally quasi-finite morphism is
locally quasi-finite. -/
@[stacks 03XL] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, IsStableUnderBaseChange
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)))

#check
  (AlgebraicGeometry.AlgebraicSpace.QuasiFinite.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
      QuasiFinite f → ∀ (g : Z ⟶ Y) [CategoryTheory.Limits.HasPullback f g],
        QuasiFinite (CategoryTheory.Limits.pullback.snd f g))
#check
  (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
      LocallyQuasiFinite f → ∀ (g : Z ⟶ Y) [CategoryTheory.Limits.HasPullback f g],
        LocallyQuasiFinite (CategoryTheory.Limits.pullback.snd f g))
