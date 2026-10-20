module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Scheme.Etale.CurveCohomology

/-- For a constructible locally torsion abelian étale sheaf on a separated finite-type
scheme of dimension at most one over an algebraically closed field, the eight étale
cohomological properties hold if and only if they hold after restriction to a dense open
subscheme followed by extension by zero. -/
theorem properties_iff_extensionByZeroRestriction
    {k : Type u} [Field k] [IsAlgClosed k]
    [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S),
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (h_torsion : IsLocallyTorsion F)
    {X' : Scheme.{u}} (j : X' ⟶ X.left) [IsOpenImmersion j]
    [∀ G : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G]
    (h_dense : DenseRange j)
    (h_constructible : IsConstructibleEtale
      (fun {Y} inclusion G ↦
        ((smallEtalePullback inclusion).sheafPullback AddCommGrpCat.{u}
          X.left.smallEtaleTopology Y.smallEtaleTopology).obj G)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    Properties X F ↔
      Properties X ((abelianExtensionByZero j).obj
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F)) := sorry

end AlgebraicGeometry.Scheme.Etale.CurveCohomology
