module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.InverseSystem

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
variable [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
variable [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasExt.{u} (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (Scheme.smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((Scheme.smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable (c : Cone D)
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : AbelianSheafSystem D) (p : ℕ)
variable [HasColimit (cohomologyDiagram D F p)]
variable [HasColimit (inverseImageDiagram D c F)]

/- Theorem 59.51.3: étale cohomology commutes with the filtered colimit of a compatible
system of abelian sheaves on a directed inverse limit of qcqs schemes with affine
transition morphisms. Writing `X = lim X_i` and `F = colim f_i⁻¹ F_i`, the comparison
`colim_i H^p_étale(X_i, F_i) ⟶ H^p_étale(X, F)` is an isomorphism for every `p ≥ 0`.
The diagrams retain all original transitions, with genuine categorical identities
adjoined; their cocones impose exactly the source transition equations. -/
@[stacks 09YQ] #check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomology_colimit_affineTransition
    (D := D) (c := c) (F := F) (p := p) :
      IsLimit c → IsIso (AlgebraicGeometry.Scheme.Etale.comparison D c F p))

end AlgebraicGeometry.Scheme.Etale

end
