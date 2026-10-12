/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.DenseOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme.Etale.CurveCohomology

universe u

/- Lemma 59.83.6: for constructible torsion abelian étale sheaves in Situation 59.83.1,
the eight cohomological properties are invariant under restriction to a dense open
subscheme followed by extension by zero. -/
@[stacks 0GJA] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.properties_iff_extensionByZeroRestriction :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
      [∀ {S T : Scheme.{u}} (f : T ⟶ S),
        ((Scheme.smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
      (h_dim : topologicalKrullDim X.left ≤ 1)
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
      (h_torsion : IsLocallyTorsion F)
      {X' : Scheme.{u}} (j : X' ⟶ X.left) [IsOpenImmersion j]
      [∀ G : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (Scheme.etaleRestriction j).op.HasLeftKanExtension G]
      (h_dense : DenseRange j)
      (h_constructible : IsConstructibleEtale
        (fun {Y} inclusion G ↦
          ((Scheme.smallEtalePullback inclusion).sheafPullback AddCommGrpCat.{u}
            X.left.smallEtaleTopology Y.smallEtaleTopology).obj G)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F),
      Properties X F ↔
        Properties X ((Scheme.abelianExtensionByZero j).obj
          ((Scheme.etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F)))
