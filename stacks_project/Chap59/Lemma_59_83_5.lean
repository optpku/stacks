module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.FinitePushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme.Etale.CurveCohomology

noncomputable section

universe u

/- Lemma 59.83.5: the eight étale cohomological properties of a locally torsion
abelian sheaf on a separated curve over an algebraically closed field are preserved
by finite pushforward. -/
@[stacks 0A5D] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofFinitePushforward :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
      [∀ {S T : Scheme.{u}} (f : T ⟶ S),
        ((Scheme.smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
      (X Y : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
      [Scheme.Hom.FiniteType Y.hom] [IsSeparated X.hom] [IsSeparated Y.hom]
      [Fact (topologicalKrullDim X.left ≤ 1)]
      [Fact (topologicalKrullDim Y.left ≤ 1)]
      (f : X.left ⟶ Y.left) [IsFinite f] (h_over : f ≫ Y.hom = X.hom)
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
      IsLocallyTorsion F → Properties X F →
        Properties Y ((Scheme.etaleAbelianPushforward f).obj F))
