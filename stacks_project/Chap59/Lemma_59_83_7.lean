module

public import stacks_project.Chap59.Lemma_59_83_2
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.Constant
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.SmoothExtensionByZero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 59.83.7. On a smooth separated finite-type scheme of dimension at most
one over an algebraically closed field, extension by zero of constant prime cyclic
coefficients along any open immersion satisfies statements (1)–(8). -/
@[stacks 03SG] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofSmoothExtensionByZeroConstantZMod :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
      [∀ {S T : Scheme.{u}} (f : T ⟶ S),
        ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom],
      topologicalKrullDim X.left ≤ 1 → ∀ [Smooth X.hom]
        (ell : ℕ) [Fact (Nat.Prime ell)]
        {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
        [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
          (etaleRestriction j).op.HasLeftKanExtension G],
      AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties X
        (AlgebraicGeometry.Etale.TorsionOnCurve.extensionByZeroConstantZMod j ell))
