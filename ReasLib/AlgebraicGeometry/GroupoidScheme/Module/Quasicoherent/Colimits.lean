/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Forget
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Colimits of equivariant quasi-coherent modules

This module constructs colimits of quasi-coherent modules on a groupoid scheme by
forming the colimit of the underlying module sheaves and descending the equivariance maps.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

section HasColimitsOfShape

variable {S : Scheme.{u}} (G : GroupoidScheme S)
variable {J : Type u} [Category.{u} J]

/-- The object scheme of the groupoid scheme. -/
private abbrev objectScheme : Scheme.{u} := G.U.left

/-- The ambient module sheaf underlying an equivariant quasi-coherent module. -/
private abbrev moduleObj (A : G.QCoh) : (objectScheme G).Modules := A.obj.obj

/-- The underlying module-sheaf diagram of a diagram of equivariant
quasi-coherent modules. -/
private abbrev moduleDiagram (F : J ⥤ G.QCoh) : J ⥤ (objectScheme G).Modules :=
  F ⋙ forget G ⋙ Scheme.QCoh.inclusion G.U.left

/-- The target pullback of the underlying module-sheaf diagram. -/
private abbrev targetPullbackDiagram (F : J ⥤ G.QCoh) : J ⥤ G.R.left.Modules :=
  moduleDiagram G F ⋙ Scheme.Modules.pullback G.t.left

/-- The source pullback of the underlying module-sheaf diagram. -/
private abbrev sourcePullbackDiagram (F : J ⥤ G.QCoh) : J ⥤ G.R.left.Modules :=
  moduleDiagram G F ⋙ Scheme.Modules.pullback G.s.left

/-- The underlying action map of one object in the diagram, expressed in the
ambient module-sheaf categories. -/
private def actionComponent (F : J ⥤ G.QCoh) (j : J) :
    (targetPullbackDiagram G F).obj j ⟶ (sourcePullbackDiagram G F).obj j :=
  eqToHom (Scheme.QCoh.pullback_obj G.t.left (F.obj j).obj).symm ≫
    (F.obj j).action.hom ≫
      eqToHom (Scheme.QCoh.pullback_obj G.s.left (F.obj j).obj)

/-- Transport the ambient module pullback map to the underlying map of a pulled-back
quasi-coherent morphism. -/
private theorem modulePullbackCompPullbackObj {X Y : Scheme.{u}} (g : Y ⟶ X)
    {F₁ F₂ : Scheme.QCoh X} (a : F₁ ⟶ F₂) :
    (Scheme.Modules.pullback g).map a.hom ≫ eqToHom (Scheme.QCoh.pullback_obj g F₂).symm =
      eqToHom (Scheme.QCoh.pullback_obj g F₁).symm ≫ ((Scheme.QCoh.pullback g).map a).hom := by
  -- Reduce both object-identification transports to identities, so the statement becomes the
  -- ambient version of `Scheme.QCoh.pullback_map`.
  cases a
  rw [Scheme.QCoh.pullback_map]
  let h₁ : ((Scheme.QCoh.pullback g).obj F₁).obj = (Scheme.Modules.pullback g).obj F₁.obj :=
    Scheme.QCoh.pullback_obj g F₁
  let h₂ : ((Scheme.QCoh.pullback g).obj F₂).obj = (Scheme.Modules.pullback g).obj F₂.obj :=
    Scheme.QCoh.pullback_obj g F₂
  cases h₁
  cases h₂
  rfl

/-- Transport the underlying map of a pulled-back quasi-coherent morphism back to the ambient
module pullback map. -/
private theorem pullbackMapHomCompPullbackObj {X Y : Scheme.{u}} (g : Y ⟶ X)
    {F₁ F₂ : Scheme.QCoh X} (a : F₁ ⟶ F₂) :
    ((Scheme.QCoh.pullback g).map a).hom ≫ eqToHom (Scheme.QCoh.pullback_obj g F₂) =
      eqToHom (Scheme.QCoh.pullback_obj g F₁) ≫ (Scheme.Modules.pullback g).map a.hom := by
  -- Reduce both object-identification transports to identities, so the statement becomes the
  -- ambient version of `Scheme.QCoh.pullback_map`.
  cases a
  rw [Scheme.QCoh.pullback_map]
  let h₁ : ((Scheme.QCoh.pullback g).obj F₁).obj = (Scheme.Modules.pullback g).obj F₁.obj :=
    Scheme.QCoh.pullback_obj g F₁
  let h₂ : ((Scheme.QCoh.pullback g).obj F₂).obj = (Scheme.Modules.pullback g).obj F₂.obj :=
    Scheme.QCoh.pullback_obj g F₂
  cases h₁
  cases h₂
  rfl

/-- Whiskering the forgotten module diagram by pullback uses ordinary pullback of the
underlying module map. -/
private theorem pullbackDiagramMap (g : G.R.left ⟶ G.U.left) (F : J ⥤ G.QCoh)
    {j j' : J} (f : j ⟶ j') :
    ((moduleDiagram G F ⋙ Scheme.Modules.pullback g).map f) =
      (Scheme.Modules.pullback g).map (F.map f).hom.hom := by
  -- Once the forgotten diagram map is normalized, whiskering by pullback is definitional.
  rfl

/-- The ambient action components commute with the structure maps of the diagram. -/
private theorem actionComponent_naturality (F : J ⥤ G.QCoh)
    {j j' : J} (f : j ⟶ j') :
    (targetPullbackDiagram G F).map f ≫ actionComponent G F j' =
      actionComponent G F j ≫ (sourcePullbackDiagram G F).map f := by
  -- Route correction: rewrite the equivariance square directly in the whiskered diagram normal
  -- form so later colimit identities can use `colimit.w` without reopening the transports.
  have hcompat :
      ((Scheme.QCoh.pullback G.t.left).map (F.map f).hom).hom ≫ (F.obj j').action.hom =
        (F.obj j).action.hom ≫ ((Scheme.QCoh.pullback G.s.left).map (F.map f).hom).hom := by
    -- Forget the equivariance square to the ambient module category once.
    simpa using congrArg (fun k => k.hom) (F.map f).compatibility
  -- Normalize both whiskered diagram maps, then transport the QCoh compatibility square across
  -- the two pullback-object identifications.
  rw [pullbackDiagramMap, pullbackDiagramMap]
  dsimp [actionComponent]
  calc
    (Scheme.Modules.pullback G.t.left).map (F.map f).hom.hom ≫
        eqToHom (Scheme.QCoh.pullback_obj G.t.left (F.obj j').obj).symm ≫
          (F.obj j').action.hom ≫
            eqToHom (Scheme.QCoh.pullback_obj G.s.left (F.obj j').obj)
      = eqToHom (Scheme.QCoh.pullback_obj G.t.left (F.obj j).obj).symm ≫
          ((Scheme.QCoh.pullback G.t.left).map (F.map f).hom).hom ≫
            (F.obj j').action.hom ≫
              eqToHom (Scheme.QCoh.pullback_obj G.s.left (F.obj j').obj) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                k ≫ (F.obj j').action.hom ≫
                  eqToHom (Scheme.QCoh.pullback_obj G.s.left (F.obj j').obj))
              (modulePullbackCompPullbackObj (g := G.t.left) (a := (F.map f).hom))
    _ = eqToHom (Scheme.QCoh.pullback_obj G.t.left (F.obj j).obj).symm ≫
          (F.obj j).action.hom ≫
            ((Scheme.QCoh.pullback G.s.left).map (F.map f).hom).hom ≫
              eqToHom (Scheme.QCoh.pullback_obj G.s.left (F.obj j').obj) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                eqToHom (Scheme.QCoh.pullback_obj G.t.left (F.obj j).obj).symm ≫
                  k ≫ eqToHom (Scheme.QCoh.pullback_obj G.s.left (F.obj j').obj))
              hcompat
    _ = eqToHom (Scheme.QCoh.pullback_obj G.t.left (F.obj j).obj).symm ≫
          (F.obj j).action.hom ≫
            eqToHom (Scheme.QCoh.pullback_obj G.s.left (F.obj j).obj) ≫
              (Scheme.Modules.pullback G.s.left).map (F.map f).hom.hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                eqToHom (Scheme.QCoh.pullback_obj G.t.left (F.obj j).obj).symm ≫
                  (F.obj j).action.hom ≫ k)
              (pullbackMapHomCompPullbackObj (g := G.s.left) (a := (F.map f).hom))

/-- Forgetting a cocone relation all the way to ambient module sheaves yields the corresponding
module-level naturality square. -/
private theorem forgetCoconeNaturality (F : J ⥤ G.QCoh) (s : Cocone F)
    {j j' : J} (f : j ⟶ j') :
    (moduleDiagram G F).map f ≫ (hom (s.ι.app j')).hom =
      (hom (s.ι.app j)).hom := by
  -- Forget the cocone equality first to quasi-coherent modules and then to ambient module sheaves.
  have hQCoh : hom (F.map f ≫ s.ι.app j') = hom (s.ι.app j) := by
    exact congrArg (fun k : F.obj j ⟶ s.pt ↦ hom k) (s.w f)
  change (hom (F.map f)).hom ≫ (hom (s.ι.app j')).hom = (hom (s.ι.app j)).hom
  exact congrArg (fun k : (F.obj j).obj ⟶ s.pt.obj ↦ k.hom) hQCoh

/-- The quasi-coherent module underlying the colimit of a diagram of equivariant
quasi-coherent modules. -/
private def colimitBase (F : J ⥤ G.QCoh) : Scheme.QCoh G.U.left :=
  ⟨colimit (moduleDiagram G F),
    Scheme.Modules.isQuasicoherent_colimit (moduleDiagram G F)
      (fun j ↦ (F.obj j).obj.property)⟩

/-- The ambient module-sheaf action on the colimit object. -/
private def colimitBaseActionHom (F : J ⥤ G.QCoh) :
    (Scheme.Modules.pullback G.t.left).obj (colimit (moduleDiagram G F)) ⟶
      (Scheme.Modules.pullback G.s.left).obj (colimit (moduleDiagram G F)) :=
  (preservesColimitIso (Scheme.Modules.pullback G.t.left) (moduleDiagram G F)).hom ≫
    colimit.desc (targetPullbackDiagram G F)
      { pt := (Scheme.Modules.pullback G.s.left).obj (colimit (moduleDiagram G F))
        ι :=
          { app := fun j ↦
              actionComponent G F j ≫
                colimit.ι (sourcePullbackDiagram G F) j ≫
                  (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                    (moduleDiagram G F)).inv
            naturality := by
              intro j j' f
              -- The action square matches the source pullback cocone after one rewrite by the
              -- normalized action naturality and one rewrite by the colimit cocone equation.
              calc
                (targetPullbackDiagram G F).map f ≫ actionComponent G F j' ≫
                    colimit.ι (sourcePullbackDiagram G F) j' ≫
                      (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                        (moduleDiagram G F)).inv
                  = actionComponent G F j ≫ (sourcePullbackDiagram G F).map f ≫
                      colimit.ι (sourcePullbackDiagram G F) j' ≫
                        (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                          (moduleDiagram G F)).inv := by
                      simpa [Category.assoc] using
                        congrArg
                          (fun k ↦
                            k ≫ colimit.ι (sourcePullbackDiagram G F) j' ≫
                              (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                                (moduleDiagram G F)).inv)
                          (actionComponent_naturality G F f)
                _ = actionComponent G F j ≫ colimit.ι (sourcePullbackDiagram G F) j ≫
                      (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                        (moduleDiagram G F)).inv := by
                      simpa [Category.assoc] using
                        congrArg
                          (fun k ↦
                            actionComponent G F j ≫ k ≫
                              (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                                (moduleDiagram G F)).inv)
                          (colimit.w (sourcePullbackDiagram G F) f) } }

/-- The equivariance morphism on the colimit base object. -/
private def colimitBaseAction (F : J ⥤ G.QCoh) :
    (Scheme.QCoh.pullback G.t.left).obj (colimitBase G F) ⟶
      (Scheme.QCoh.pullback G.s.left).obj (colimitBase G F) :=
  ObjectProperty.homMk
    (eqToHom (Scheme.QCoh.pullback_obj G.t.left (colimitBase G F)) ≫
      colimitBaseActionHom G F ≫
        eqToHom (Scheme.QCoh.pullback_obj G.s.left (colimitBase G F)).symm)

/-- Precomposing the descended ambient colimit action with a colimit leg recovers the
corresponding diagram action. -/
private theorem colimitBaseActionHom_ι (F : J ⥤ G.QCoh) (j : J) :
    (Scheme.Modules.pullback G.t.left).map (colimit.ι (moduleDiagram G F) j) ≫
      colimitBaseActionHom G F =
    actionComponent G F j ≫
      colimit.ι (moduleDiagram G F ⋙ Scheme.Modules.pullback G.s.left) j ≫
        (preservesColimitIso (Scheme.Modules.pullback G.s.left)
          (moduleDiagram G F)).inv := by
  -- Rewrite the descended action through the preserved-colimit comparison and the colimit
  -- descent formula for the target pullback diagram.
  dsimp [colimitBaseActionHom]
  erw [CategoryTheory.ι_preservesColimitIso_hom_assoc]
  change colimit.ι (targetPullbackDiagram G F) j ≫
      colimit.desc (targetPullbackDiagram G F)
        { pt := (Scheme.Modules.pullback G.s.left).obj (colimit (moduleDiagram G F))
          ι :=
            { app := fun j ↦
                actionComponent G F j ≫
                  colimit.ι (sourcePullbackDiagram G F) j ≫
                    (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                      (moduleDiagram G F)).inv
              naturality := by
                intro j j' f
                -- This is exactly the normalized naturality proved in `colimitBaseActionHom`.
                calc
                  (targetPullbackDiagram G F).map f ≫ actionComponent G F j' ≫
                      colimit.ι (sourcePullbackDiagram G F) j' ≫
                        (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                          (moduleDiagram G F)).inv
                    = actionComponent G F j ≫ (sourcePullbackDiagram G F).map f ≫
                        colimit.ι (sourcePullbackDiagram G F) j' ≫
                          (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                            (moduleDiagram G F)).inv := by
                        simpa [Category.assoc] using
                          congrArg
                            (fun k ↦
                              k ≫ colimit.ι (sourcePullbackDiagram G F) j' ≫
                                (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                                  (moduleDiagram G F)).inv)
                            (actionComponent_naturality G F f)
                  _ = actionComponent G F j ≫ colimit.ι (sourcePullbackDiagram G F) j ≫
                        (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                          (moduleDiagram G F)).inv := by
                        simpa [Category.assoc] using
                          congrArg
                            (fun k ↦
                              actionComponent G F j ≫ k ≫
                                (preservesColimitIso (Scheme.Modules.pullback G.s.left)
                                  (moduleDiagram G F)).inv)
                            (colimit.w (sourcePullbackDiagram G F) f) } } =
    actionComponent G F j ≫
      colimit.ι (moduleDiagram G F ⋙ Scheme.Modules.pullback G.s.left) j ≫
        (preservesColimitIso (Scheme.Modules.pullback G.s.left)
          (moduleDiagram G F)).inv
  erw [CategoryTheory.Limits.colimit.ι_desc]
  rfl

/-- The colimit action restricts along each cocone leg to the original equivariant action. -/
private theorem colimitBaseAction_ι (F : J ⥤ G.QCoh) (j : J) :
    let ιj : (F.obj j).obj ⟶ colimitBase G F :=
      ObjectProperty.homMk
        (colimit.ι (moduleDiagram G F) j : (F.obj j).obj.obj ⟶ (colimitBase G F).obj)
    (Scheme.QCoh.pullback G.t.left).map
        ιj ≫
      colimitBaseAction G F =
    (F.obj j).action ≫
      (Scheme.QCoh.pullback G.s.left).map
        ιj := sorry

/-- The colimit action satisfies the cocycle condition. -/
private theorem colimitBaseAction_cocycle (F : J ⥤ G.QCoh) :
    Cocycle G (colimitBase G F) (colimitBaseAction G F) := sorry

/-- The colimit action satisfies the unit condition. -/
private theorem colimitBaseAction_unit (F : J ⥤ G.QCoh) :
    Unit G (colimitBase G F) (colimitBaseAction G F) := sorry

/-- The colimit object in the equivariant quasi-coherent category. -/
private def colimitObj (F : J ⥤ G.QCoh) : G.QCoh :=
  of (colimitBase G F) (colimitBaseAction G F)
    (colimitBaseAction_cocycle G F) (colimitBaseAction_unit G F)

/-- Each underlying colimit leg is compatible with the equivariance maps. -/
private theorem colimitι_compatibility (F : J ⥤ G.QCoh) (j : J) :
    let ιj : (F.obj j).obj ⟶ colimitBase G F :=
      ObjectProperty.homMk
        (colimit.ι (moduleDiagram G F) j : (F.obj j).obj.obj ⟶ (colimitBase G F).obj)
    (Scheme.QCoh.pullback G.t.left).map ιj ≫ (colimitObj G F).action =
      (F.obj j).action ≫ (Scheme.QCoh.pullback G.s.left).map ιj := sorry

/-- The colimit cocone legs, built from the ambient colimit maps of module
sheaves. -/
private def colimitι (F : J ⥤ G.QCoh) (j : J) : F.obj j ⟶ colimitObj G F :=
  let ιj : (F.obj j).obj ⟶ colimitBase G F :=
    ObjectProperty.homMk
      (colimit.ι (moduleDiagram G F) j : (F.obj j).obj.obj ⟶ (colimitBase G F).obj)
  System.Hom.of ιj (colimitι_compatibility G F j)

/-- The equivariant colimit legs are natural in the indexing category. -/
private theorem colimitCocone_naturality (F : J ⥤ G.QCoh)
    {j j' : J} (f : j ⟶ j') :
    F.map f ≫ colimitι G F j' = colimitι G F j := sorry

/-- The colimit cocone in `G.QCoh`, with pointwise underlying module colimit. -/
private def colimitCocone (F : J ⥤ G.QCoh) : Cocone F where
  pt := colimitObj G F
  ι :=
    { app := fun j ↦ colimitι G F j
      naturality := fun _ _ f ↦ colimitCocone_naturality G F f }

/-- Forget the target cocone to a cocone of ambient module sheaves. -/
private def descModuleCocone (F : J ⥤ G.QCoh) (s : Cocone F) :
    Cocone (moduleDiagram G F) where
  pt := moduleObj G s.pt
  ι :=
    { app := fun j ↦ (hom (s.ι.app j)).hom
      naturality := fun _ _ f ↦ forgetCoconeNaturality G F s f }

/-- The morphism descended from an ambient module cocone is compatible with equivariance. -/
private theorem descHom_compatibility (F : J ⥤ G.QCoh) (s : Cocone F) :
    (Scheme.QCoh.pullback G.t.left).map
        (ObjectProperty.homMk
          (colimit.desc (moduleDiagram G F) (descModuleCocone G F s) :
            (colimitBase G F).obj ⟶ moduleObj G s.pt)) ≫
      s.pt.action =
    (colimitObj G F).action ≫
      (Scheme.QCoh.pullback G.s.left).map
        (ObjectProperty.homMk
          (colimit.desc (moduleDiagram G F) (descModuleCocone G F s) :
            (colimitBase G F).obj ⟶ moduleObj G s.pt)) := sorry

/-- The descended morphism from the equivariant colimit object to any cocone
point, built from the ambient module colimit universal property. -/
private def descHom (F : J ⥤ G.QCoh) (s : Cocone F) : colimitObj G F ⟶ s.pt :=
  System.Hom.of
    (ObjectProperty.homMk
      (colimit.desc (moduleDiagram G F) (descModuleCocone G F s) :
        (colimitBase G F).obj ⟶ moduleObj G s.pt))
    (descHom_compatibility G F s)

/-- The descended morphism factors every leg of the equivariant colimit cocone. -/
private theorem colimitIsColimit_fac (F : J ⥤ G.QCoh) (s : Cocone F) (j : J) :
    colimitι G F j ≫ descHom G F s = s.ι.app j := sorry

/-- A morphism from the equivariant colimit is determined by its composites with the
colimit legs. -/
private theorem colimitIsColimit_uniq (F : J ⥤ G.QCoh) (s : Cocone F)
    (m : colimitObj G F ⟶ s.pt)
    (hm : ∀ j, colimitι G F j ≫ m = s.ι.app j) :
    m = descHom G F s := sorry

/-- The explicit colimit cocone is universal. -/
private def colimitIsColimit (F : J ⥤ G.QCoh) :
    IsColimit (colimitCocone G F) where
  desc := descHom G F
  fac := colimitIsColimit_fac G F
  uniq := colimitIsColimit_uniq G F

/-- For every small same-universe indexing category `J`, equivariant
quasi-coherent modules on a groupoid scheme admit `J`-shaped colimits. -/
theorem hasColimitsOfShape : HasColimitsOfShape J G.QCoh where
  has_colimit F := ⟨⟨colimitCocone G F, colimitIsColimit G F⟩⟩

end HasColimitsOfShape

/-- Equivariant quasi-coherent modules on a groupoid scheme admit all
same-universe small colimits. -/
theorem hasColimits {S : Scheme.{u}}
    (G : GroupoidScheme S) : HasColimits G.QCoh where
  has_colimits_of_shape J _ := hasColimitsOfShape (J := J) G

end AlgebraicGeometry.GroupoidScheme.QCoh
