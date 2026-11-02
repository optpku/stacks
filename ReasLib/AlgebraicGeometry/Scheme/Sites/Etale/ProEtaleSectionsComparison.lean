/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleFullyFaithful

/-!
# Sections of the étale inverse image along inverse systems

Stage diagrams and canonical colimit comparisons for sections of the
étale-to-pro-étale inverse image along cones in the pro-étale site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Preorder I]
variable {X : Scheme.{u}}
variable [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension P]
variable [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]

section proEtStages

variable (D : OrderDual I ⥤ X.ProEt)

/-- The `I`-diagram of sections `ε⁻¹ F(Y_i)` of a sheaf of sets pulled back
along `etaleToProEt`. -/
def etaleToProEtPullbackSectionsDiagram
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) : I ⥤ Type (u + 1) where
  obj i :=
    ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj
      (op (D.obj (OrderDual.toDual i)))
  map {i j} hij :=
    ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.map
      (op (OrderDualInverseSystem.transitionMap D (leOfHom hij)))
  map_id := by
    intro i
    let G := ((etaleToProEtPullback X (Type (u + 1))).obj F).obj
    exact (congrArg (fun h : D.obj (OrderDual.toDual i) ⟶ D.obj (OrderDual.toDual i) ↦
      G.map h.op) (D.map_id (OrderDual.toDual i))).trans (G.map_id _)
  map_comp := by
    intro i j k f g
    let G := ((etaleToProEtPullback X (Type (u + 1))).obj F).obj
    exact (congrArg (fun h : D.obj (OrderDual.toDual k) ⟶ D.obj (OrderDual.toDual i) ↦
      G.map h.op) (D.map_comp
        (homOfLE (OrderDual.toDual_le_toDual.mpr (leOfHom g)))
        (homOfLE (OrderDual.toDual_le_toDual.mpr (leOfHom f))))).trans (G.map_comp _ _)

/-- Evaluating the sections diagram recovers `ε⁻¹ F` at the corresponding
stage of `D`. -/
theorem etaleToProEtPullbackSectionsDiagram_obj
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (i : I) :
    (etaleToProEtPullbackSectionsDiagram D F).obj i =
      ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj
        (op (D.obj (OrderDual.toDual i))) := rfl

variable (c : Cone D)

/-- The canonical comparison `colim ε⁻¹ F(Y_i) ⟶ ε⁻¹ F(Y)` obtained by
restricting along the legs of a cone in `X.ProEt`. -/
def etaleToProEtPullbackSectionsComparison
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [HasColimit (etaleToProEtPullbackSectionsDiagram D F)] :
    colimit (etaleToProEtPullbackSectionsDiagram D F) ⟶
      ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj (op c.pt) :=
  colimit.desc (etaleToProEtPullbackSectionsDiagram D F)
    { pt := ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj (op c.pt)
      ι :=
        { app := fun i ↦
            ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.map
              (op (c.π.app (OrderDual.toDual i)))
          naturality := by
            intro i j f
            let G := ((etaleToProEtPullback X (Type (u + 1))).obj F).obj
            change G.map (OrderDualInverseSystem.transitionMap D (leOfHom f)).op ≫
                G.map (c.π.app (OrderDual.toDual j)).op =
              G.map (c.π.app (OrderDual.toDual i)).op
            exact (G.map_comp _ _).symm.trans
              (congrArg (fun h : c.pt ⟶ D.obj (OrderDual.toDual i) ↦ G.map h.op)
                (c.w (homOfLE (OrderDual.toDual_le_toDual.mpr (leOfHom f))))) } }

/-- The comparison morphism restricts along colimit inclusions to restriction
along the corresponding cone leg. -/
theorem etaleToProEtPullbackSectionsComparison_ι
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [HasColimit (etaleToProEtPullbackSectionsDiagram D F)] (i : I) :
    colimit.ι (etaleToProEtPullbackSectionsDiagram D F) i ≫
      etaleToProEtPullbackSectionsComparison D c F =
      ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.map
        (op (c.π.app (OrderDual.toDual i))) := by
  unfold etaleToProEtPullbackSectionsComparison
  exact colimit.ι_desc _ i

end proEtStages

section etaleStages

variable (E : OrderDual I ⥤ X.Etale)

/-- The `I`-diagram of sections `F(Y_i)` for an inverse system of objects of
`X.Etale`. -/
def etaleToProEtPullbackEtaleSectionsDiagram
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) : I ⥤ Type (u + 1) where
  obj i := F.obj.obj (op (E.obj (OrderDual.toDual i)))
  map {i j} hij :=
    F.obj.map (op (OrderDualInverseSystem.transitionMap E (leOfHom hij)))
  map_id := by
    intro i
    exact (congrArg (fun h : E.obj (OrderDual.toDual i) ⟶ E.obj (OrderDual.toDual i) ↦
      F.obj.map h.op) (E.map_id (OrderDual.toDual i))).trans (F.obj.map_id _)
  map_comp := by
    intro i j k f g
    exact (congrArg (fun h : E.obj (OrderDual.toDual k) ⟶ E.obj (OrderDual.toDual i) ↦
      F.obj.map h.op) (E.map_comp
        (homOfLE (OrderDual.toDual_le_toDual.mpr (leOfHom g)))
        (homOfLE (OrderDual.toDual_le_toDual.mpr (leOfHom f))))).trans (F.obj.map_comp _ _)

/-- Evaluating the étale-stage sections diagram recovers `F` at the
corresponding stage of `E`. -/
theorem etaleToProEtPullbackEtaleSectionsDiagram_obj
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (i : I) :
    (etaleToProEtPullbackEtaleSectionsDiagram E F).obj i =
      F.obj.obj (op (E.obj (OrderDual.toDual i))) := rfl

variable (c : Cone (E ⋙ etaleToProEt X))

/-- The canonical comparison `colim F(Y_i) ⟶ ε⁻¹ F(Y)` obtained by the
étale-to-pro-étale unit followed by restriction along the cone legs. -/
def etaleToProEtPullbackEtaleSectionsComparison
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [HasColimit (etaleToProEtPullbackEtaleSectionsDiagram E F)] :
    colimit (etaleToProEtPullbackEtaleSectionsDiagram E F) ⟶
      ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj (op c.pt) :=
  colimit.desc (etaleToProEtPullbackEtaleSectionsDiagram E F)
    { pt := ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj (op c.pt)
      ι :=
        { app := fun i ↦
            EtaleToProEt.obj_etale X F (E.obj (OrderDual.toDual i)) ≫
              ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.map
                (op (c.π.app (OrderDual.toDual i)))
          naturality := by
            intro i j f
            let G := ((etaleToProEtPullback X (Type (u + 1))).obj F).obj
            let η := ((etaleToProEt_sheafAdjunction X (Type (u + 1))).unit.app F).hom
            have hη := η.naturality
              (op (OrderDualInverseSystem.transitionMap E (leOfHom f)))
            change F.obj.map (op (OrderDualInverseSystem.transitionMap E (leOfHom f))) ≫
                η.app (op (E.obj (OrderDual.toDual j))) =
              η.app (op (E.obj (OrderDual.toDual i))) ≫
                G.map (op ((E ⋙ etaleToProEt X).map (homOfLE _))) at hη
            change F.obj.map (op (OrderDualInverseSystem.transitionMap E (leOfHom f))) ≫
                (η.app (op (E.obj (OrderDual.toDual j))) ≫
                  G.map (op (c.π.app (OrderDual.toDual j)))) =
              (η.app (op (E.obj (OrderDual.toDual i))) ≫
                G.map (op (c.π.app (OrderDual.toDual i)))) ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, hη, Category.assoc]
            apply congrArg (fun h ↦ η.app (op (E.obj (OrderDual.toDual i))) ≫ h)
            exact (G.map_comp _ _).symm.trans
              (congrArg (fun h : c.pt ⟶ (E ⋙ etaleToProEt X).obj (OrderDual.toDual i) ↦
                G.map h.op)
                (c.w (homOfLE (OrderDual.toDual_le_toDual.mpr (leOfHom f))))) } }

/-- The étale-stage comparison restricts along colimit inclusions to the
unit of `ε⁻¹ ⊣ ε_*` followed by restriction along the cone leg. -/
theorem etaleToProEtPullbackEtaleSectionsComparison_ι
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [HasColimit (etaleToProEtPullbackEtaleSectionsDiagram E F)] (i : I) :
    colimit.ι (etaleToProEtPullbackEtaleSectionsDiagram E F) i ≫
      etaleToProEtPullbackEtaleSectionsComparison E c F =
      EtaleToProEt.obj_etale X F (E.obj (OrderDual.toDual i)) ≫
        ((etaleToProEtPullback X (Type (u + 1))).obj F).obj.map
          (op (c.π.app (OrderDual.toDual i))) := by
  unfold etaleToProEtPullbackEtaleSectionsComparison
  exact colimit.ι_desc _ i

/-- On every colimit inclusion, the étale-stage comparison factors through
`EtaleToProEt.obj_etale` and the pro-étale-stage comparison. -/
theorem etaleToProEtPullbackEtaleSectionsComparison_comp
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [HasColimit (etaleToProEtPullbackEtaleSectionsDiagram E F)]
    [HasColimit (etaleToProEtPullbackSectionsDiagram (E ⋙ etaleToProEt X) F)]
    (i : I) :
    colimit.ι (etaleToProEtPullbackEtaleSectionsDiagram E F) i ≫
      etaleToProEtPullbackEtaleSectionsComparison E c F =
      EtaleToProEt.obj_etale X F (E.obj (OrderDual.toDual i)) ≫
        colimit.ι (etaleToProEtPullbackSectionsDiagram (E ⋙ etaleToProEt X) F) i ≫
          etaleToProEtPullbackSectionsComparison (E ⋙ etaleToProEt X) c F := by
  rw [etaleToProEtPullbackEtaleSectionsComparison_ι,
    etaleToProEtPullbackSectionsComparison_ι]

end etaleStages

variable [Nonempty I] [IsDirected I (· ≤ ·)]

section proEtStages

variable (D : OrderDual I ⥤ X.ProEt)
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap D hij).left]
variable [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i)).left]
variable [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i)).left]
variable (c : Cone D)
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
variable [HasColimit (etaleToProEtPullbackSectionsDiagram D F)]

/-- Sections of the étale inverse image on a directed inverse limit of
quasi-compact and quasi-separated pro-étale objects with affine transitions
are the colimit of the stage sections, via the canonical comparison. -/
theorem etaleToProEtPullback_sectionsColimit
    (hc : IsLimit ((ProEt.forget X ⋙ Over.forget X).mapCone c)) :
    IsIso (etaleToProEtPullbackSectionsComparison D c F) := sorry

end proEtStages

section etaleStages

variable (E : OrderDual I ⥤ X.Etale)
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap (E ⋙ etaleToProEt X) hij).left]
variable [∀ i : I, CompactSpace ((E ⋙ etaleToProEt X).obj (OrderDual.toDual i)).left]
variable [∀ i : I, QuasiSeparatedSpace ((E ⋙ etaleToProEt X).obj (OrderDual.toDual i)).left]
variable (c : Cone (E ⋙ etaleToProEt X))
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
variable [HasColimit (etaleToProEtPullbackEtaleSectionsDiagram E F)]

/-- Sections of the étale inverse image on a directed inverse limit of
quasi-compact and quasi-separated étale objects with affine transitions
are the colimit of the original étale sheaf's stage sections. -/
theorem etaleToProEtPullback_etaleSectionsColimit
    (hc : IsLimit ((ProEt.forget X ⋙ Over.forget X).mapCone c)) :
    IsIso (etaleToProEtPullbackEtaleSectionsComparison E c F) := by
  let τ : etaleToProEtPullbackEtaleSectionsDiagram E F ⟶
      etaleToProEtPullbackSectionsDiagram (E ⋙ etaleToProEt X) F :=
    { app := fun i ↦ EtaleToProEt.obj_etale X F (E.obj (OrderDual.toDual i))
      naturality := by
        intro i j f
        exact ((etaleToProEt_sheafAdjunction X (Type (u + 1))).unit.app F).hom.naturality
          (OrderDualInverseSystem.transitionMap E (leOfHom f)).op }
  haveI : ∀ i, IsIso (τ.app i) := fun i ↦
    EtaleToProEt.obj_etale_isIso X F (E.obj (OrderDual.toDual i))
  haveI : IsIso τ := NatIso.isIso_of_isIso_app τ
  letI : HasColimit (etaleToProEtPullbackSectionsDiagram (E ⋙ etaleToProEt X) F) :=
    inferInstance
  haveI : IsIso (etaleToProEtPullbackSectionsComparison (E ⋙ etaleToProEt X) c F) :=
    etaleToProEtPullback_sectionsColimit (E ⋙ etaleToProEt X) c F hc
  have h : etaleToProEtPullbackEtaleSectionsComparison E c F =
      colimMap τ ≫ etaleToProEtPullbackSectionsComparison (E ⋙ etaleToProEt X) c F := by
    apply colimit.hom_ext
    intro i
    rw [etaleToProEtPullbackEtaleSectionsComparison_ι, ← Category.assoc,
      ι_colimMap, Category.assoc, etaleToProEtPullbackSectionsComparison_ι]
  rw [h]
  infer_instance

end etaleStages

end AlgebraicGeometry.Scheme
