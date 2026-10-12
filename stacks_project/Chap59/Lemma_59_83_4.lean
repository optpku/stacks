/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme.Etale.CurveCohomology

universe u

/- Lemma 59.83.4: the eight étale cohomological conditions for torsion abelian sheaves
on a separated finite-type scheme of dimension at most one over an algebraically closed
field are preserved by short exact extensions. -/
@[stacks 0A5C] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofShortExact :
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
      (sequence : ShortComplex (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})),
      sequence.ShortExact →
        IsLocallyTorsion sequence.X₁ → IsLocallyTorsion sequence.X₂ →
        IsLocallyTorsion sequence.X₃ →
        Properties X sequence.X₁ → Properties X sequence.X₃ → Properties X sequence.X₂)
