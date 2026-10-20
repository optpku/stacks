module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.DerivedPushforward
import StacksCheckRecall

/-!
# Lemma 61.17.2

Restriction of `Rf_big,*` to a small pro-étale site agrees with `Rf_small,*`
of the restriction, and the same comparison holds after cartesian base change
on both the small and the big sites.
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived.Over

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.17.2. Restriction of the big derived direct image to the small site. -/
@[stacks 0F68]
#check (AlgebraicGeometry.Scheme.ProEt.restrict_bigDerivedPushforward :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((iInverseImage (𝟙 S)).mapDerivedCategory.obj
        ((bigDerivedPushforward f).obj K))
      ((smallDerivedPushforward f).obj
        ((iInverseImage (𝟙 T)).mapDerivedCategory.obj K)))

/- The cartesian comparison after relocalization to the small site. -/
#check (AlgebraicGeometry.Scheme.ProEt.iInverseImage_bigDerivedPushforward :
  ∀
    {S T S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (_sq : IsPullback g' f' f g)
    [HasSheafify (topology S') AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T') AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((iInverseImage g).mapDerivedCategory.obj
        ((bigDerivedPushforward f).obj K))
      ((smallDerivedPushforward f').obj
        ((iInverseImage g').mapDerivedCategory.obj K)))

section BigBaseChange

variable {S T S' T' : Scheme.{u}}
variable (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
variable (sq : IsPullback g' f' f g)
variable [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
variable [HasSheafify (proetaleTopology.over S') AddCommGrpCat.{u + 1}]
variable [HasSheafify (proetaleTopology.over T') AddCommGrpCat.{u + 1}]
variable [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (Over.map f).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over T')ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (Over.map f').op.HasPointwiseRightKanExtension P]

/- The canonical base-change transformation on the big sites is invertible. -/
#check (CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.map_isIso
    proetaleTopology g' f' f g sq :
  IsIso (BaseChange.map proetaleTopology g' f' f g sq.w))

/- Its isomorphism at every unbounded derived abelian sheaf. -/
#check (CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.appIso
    proetaleTopology g' f' f g sq :
  ∀ K : DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1}),
    (Derived.Over.pullback proetaleTopology g).obj
        ((Derived.Over.pushforward proetaleTopology f).obj K) ≅
      (Derived.Over.pushforward proetaleTopology f').obj
        ((Derived.Over.pullback proetaleTopology g').obj K))

end BigBaseChange

end AlgebraicGeometry.Scheme.ProEt
