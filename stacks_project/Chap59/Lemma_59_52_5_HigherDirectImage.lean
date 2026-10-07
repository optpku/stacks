module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.Complex
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {T U : Scheme.{u}} (f : U ⟶ T)
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    T.smallEtaleTopology U.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        T.smallEtaleTopology U.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/- The compatibility surface for the total derived étale pushforward is owned by ReasLib. -/
#check (etaleAbelianPushforwardDerived f :
    DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))

end AlgebraicGeometry.Scheme.Etale

end
