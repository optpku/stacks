module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Stalk
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.3.11: for a separated, locally finite-type morphism, restriction
to the geometric fibre canonically identifies the lower-shriek stalk with
compactly supported global sections on that fibre. -/
@[stacks 0F76] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekStalkCompactSupportIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      (ybar : GeometricPoint Y) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj
          ((etaleLowerShriek f).obj F) ≅
        AddCommGrpCat.of
          (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
            (abelianPullbackAlong (pullback.snd ybar.hom f) F)))

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekStalkCompactSupportIso_hom :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (ybar : GeometricPoint Y) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    (etaleLowerShriekStalkCompactSupportIso f ybar F).hom =
      etaleLowerShriekStalkToCompactSupport f ybar F)
