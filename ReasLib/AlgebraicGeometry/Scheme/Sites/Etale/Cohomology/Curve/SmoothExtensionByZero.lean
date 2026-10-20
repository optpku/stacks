module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.Constant
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Constant
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.DenseOpen

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.CurveCohomology

/-- On a smooth separated finite-type scheme of dimension at most one over an
algebraically closed field, extension by zero of constant prime cyclic coefficients
along any open immersion satisfies the eight étale cohomological vanishing,
finiteness, base-change, and open-restriction properties. -/
theorem Properties.ofSmoothExtensionByZeroConstantZMod
    {k : Type u} [Field k] [IsAlgClosed k]
    [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S),
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1) [Smooth X.hom]
    (ell : ℕ) [Fact (Nat.Prime ell)]
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G] :
    Properties X (AlgebraicGeometry.Etale.TorsionOnCurve.extensionByZeroConstantZMod j ell) :=
  sorry

end AlgebraicGeometry.Scheme.Etale.CurveCohomology
