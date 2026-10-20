/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Cohomology.Map

/-!
# Étale cohomology diagrams of affine-transition inverse limits

This module owns the `I`-diagram of global étale cohomology groups of a compatible
abelian sheaf system, and the canonical comparison morphism to the cohomology of
the colimit inverse-image sheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasExt.{u} (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [hAdj : ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable (c : Cone D)
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : AbelianSheafSystem D)
variable (p : ℕ)

/-- The diagram of global étale cohomology groups `H^p(X_i, F_i)`, retaining the original
transitions and adjoining genuine categorical identities. -/
def cohomologyDiagram : PreorderWithAdjoinedIdentities I ⥤ AddCommGrpCat.{u} :=
  PreorderWithAdjoinedIdentities.lift
    (fun i => (F.obj i).H' p (globalEtale (D.obj (OrderDual.toDual i))))
    (fun {i j} hij =>
      cohomologyPullback (OrderDualInverseSystem.transitionMap D hij) (F.obj i) p ≫
        Sheaf.cohomologyMap (F.transition hij) p
          (globalEtale (D.obj (OrderDual.toDual j)))) sorry

/-- Evaluating `cohomologyDiagram` recovers global étale cohomology of the stage sheaf. -/
theorem cohomologyDiagram_obj (i : I) :
    (cohomologyDiagram D F p).obj i =
      (F.obj i).H' p (globalEtale (D.obj (OrderDual.toDual i))) := sorry

/-- The cone point is the value of the constant diagram at every index. -/
instance conePoint_hasSheafify (i : I) :
    HasSheafify (((Functor.const (OrderDual I)).obj c.pt).obj
        (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u})

/-- Weak sheafification on the cone point, in constant-diagram form. -/
instance conePoint_hasWeakSheafify (i : I) :
    HasWeakSheafify (((Functor.const (OrderDual I)).obj c.pt).obj
        (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u})

/-- Ext groups on the cone point, in constant-diagram form. -/
instance conePoint_hasExt (i : I) :
    HasExt.{u} (Sheaf (((Functor.const (OrderDual I)).obj c.pt).obj
        (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) :=
  inferInstanceAs (HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}))

/-- The canonical comparison `colim_i H^p(X_i, F_i) ⟶ H^p(X, colim f_i⁻¹ F_i)`. -/
def comparison [HasColimit (cohomologyDiagram D F p)]
    [HasColimit (inverseImageDiagram D c F)] :
    colimit (cohomologyDiagram D F p) ⟶
      (colimitInverseImage D c F).H' p (globalEtale c.pt) :=
  colimit.desc (cohomologyDiagram D F p)
    { pt := (colimitInverseImage D c F).H' p (globalEtale c.pt)
      ι :=
        { app := fun i =>
            cohomologyPullback (c.π.app (OrderDual.toDual i)) (F.obj i) p ≫
              Sheaf.cohomologyMap (colimitInverseImage_ι D c F i) p (globalEtale c.pt)
          naturality := sorry } }

/-- The étale cohomology comparison is an isomorphism for affine-transition inverse limits of
qcqs schemes and compatible abelian sheaf systems. -/
theorem etaleCohomology_colimit_affineTransition
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    (hc : IsLimit c) :
    IsIso (comparison D c F p) := sorry

end AlgebraicGeometry.Scheme.Etale

end
