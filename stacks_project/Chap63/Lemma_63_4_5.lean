module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Properties
public import stacks_project.Chap59.Proposition_59_55_2_Over
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.4.5. Compact-support direct image along a locally quasi-finite
morphism has stalks naturally isomorphic to the coproduct of the stalks over
same-field geometric lifts, is exact, and commutes with direct sums. -/
@[stacks 0F5F] #check (AlgebraicGeometry.Scheme.Etale.lowerShriekStalkIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] (ybar : GeometricPoint Y),
    lowerShriek f ⋙ (toSmallEtalePoint ybar).sheafFiber ≅
      abelianStalkCoproduct f ybar)

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekStalkIso_app :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    (toSmallEtalePoint ybar).sheafFiber.obj ((lowerShriek f).obj F) ≅
      (abelianStalkCoproduct f ybar).obj F)

#check (AlgebraicGeometry.Scheme.Etale.lowerShriek_exact :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}],
    exactFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (lowerShriek f))

#check (AlgebraicGeometry.Scheme.Etale.lowerShriek_preservesFiniteLimits :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] [LocallyOfFiniteType f],
    PreservesFiniteLimits (lowerShriek f))

#check (AlgebraicGeometry.Scheme.Etale.lowerShriek_preservesFiniteColimits :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] [LocallyOfFiniteType f],
    PreservesFiniteColimits (lowerShriek f))

#check (AlgebraicGeometry.Scheme.Etale.lowerShriek_preservesCoproducts :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] [LocallyOfFiniteType f]
    {I : Type u}, PreservesColimitsOfShape (Discrete I) (lowerShriek f))
