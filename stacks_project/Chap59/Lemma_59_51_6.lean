module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions
  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
/- Lemma 59.51.6 (1) -/
@[stacks 03Q8] #check
  (AlgebraicGeometry.Scheme.higherDirectImage_sheafification :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (p : ℕ),
      IsIsomorphic
        (Sheaf.higherDirectImage (smallEtalePullback f) F p)
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
          (etalePullbackCohomologyPresheaf f F p)))

/- Lemma 59.51.6 (2) -/
@[stacks 03Q8] #check
  (AlgebraicGeometry.Scheme.derivedHigherDirectImage_sheafification :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (q : ℤ),
      IsIsomorphic
        ((DerivedCategory.homologyFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) q).obj
          ((RightDerived.Cochain.functor
            ((smallEtalePullback f).sheafPushforwardContinuous
              AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology)).obj K))
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
          (etalePullbackDerivedCohomologyPresheaf f K q)))

end AlgebraicGeometry.Scheme
