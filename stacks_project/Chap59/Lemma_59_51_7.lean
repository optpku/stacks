/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap59.Lemma_59_51_7_HigherDirectImage

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (S : Scheme.{u})
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I,
    HasInjectiveResolutions
      (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable (g : ∀ i : I, D.obj (OrderDual.toDual i) ⟶ S)
variable (hg : ∀ (i j : I) (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap D hij ≫ g i = g j)
variable [∀ i : I, QuasiCompact (g i)]
variable [∀ i : I, QuasiSeparated (g i)]
variable (c : Cone D)
variable (gX : c.pt ⟶ S)
variable (hgX : ∀ i : I, c.π.app (OrderDual.toDual i) ≫ g i = gX)
variable [QuasiCompact gX] [QuasiSeparated gX]
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : AbelianSheafSystem D) (p : ℕ)
variable [HasColimit (inverseImageDiagram D c F)]
variable [HasColimit (higherDirectImageDiagram S D g hg F p)]
variable (hc : IsLimit c)

/- Lemma 59.51.7: higher direct images commute with the colimit of an affine-transition inverse
system of schemes over a base scheme. -/
@[stacks 09Z1] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImage_colimit_affineTransition
    (S := S) (D := D) (g := g) (hg := hg) (c := c) (gX := gX) (hgX := hgX)
    (F := F) (p := p) (hc := hc) :
      IsIso (higherDirectImageComparison (S := S) (D := D) (g := g) (hg := hg)
        (c := c) (gX := gX) (hgX := hgX) (F := F) (p := p)))

end AlgebraicGeometry.Scheme.Etale

end
