module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.AlgebraBaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.AlgebraBaseChange

open AlgebraicGeometry.Scheme.AlgebraBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (A : CommRingCat.{u}) (B : I ⥤ CommRingCat.{u})
variable (σ : (Functor.const I).obj A ⟶ B)
variable {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A))
variable [QuasiCompact f] [QuasiSeparated f]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasSheafify (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasExt.{u} (Sheaf (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u})]
variable [HasColimit B]
variable [HasSheafify (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {S T : Scheme.{u}} (g : T ⟶ S),
    ((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable (p : ℕ)
variable [HasColimit (cohomologyDiagram A B σ f F p)]

/- Lemma 59.51.5: for a directed system of `A`-algebras with `B = colim B_i`, a
quasi-compact quasi-separated morphism `X ⟶ Spec(A)`, and an abelian sheaf `F`
on `X_étale`, étale cohomology of the inverse-image sheaves on the base changes
`Y_i = X ×_Spec(A) Spec(B_i)` and `Y = X ×_Spec(A) Spec(B)` commutes with the
filtered colimit. The comparison `colim_i H^p_étale(Y_i, G_i) ⟶ H^p_étale(Y, G)`
is an isomorphism for every `p ≥ 0`. -/
@[stacks 03Q6] #check
  (AlgebraicGeometry.Scheme.Etale.AlgebraBaseChange.comparison_isIso
    (A := A) (B := B) (σ := σ) (f := f) (F := F) (p := p) :
      IsIso (AlgebraicGeometry.Scheme.Etale.AlgebraBaseChange.comparison A B σ f F p))

end AlgebraicGeometry.Scheme.Etale.AlgebraBaseChange

end
