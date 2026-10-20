/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Extending an étale relation along an open immersion

Representable étale charts over presheaves have scheme-valued kernel pairs.
Gluing a kernel pair to a scheme along its diagonal extends its two projections.
Cartesian transitions of charts and open subschemes induce cartesian source squares.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation.ExtendOpen

/-- The scheme representing the kernel pair of a representable étale chart. -/
noncomputable def fiberProduct {W : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w) : Scheme.{u} :=
  hw.rep.pullback w

/-- The first scheme projection of the represented kernel pair. -/
noncomputable def fiberProductFst {W : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w) :
    fiberProduct w hw ⟶ W :=
  hw.rep.fst' w

/-- The second scheme projection of the represented kernel pair. -/
noncomputable def fiberProductSnd {W : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w) :
    fiberProduct w hw ⟶ W :=
  hw.rep.snd w

/-- The represented kernel pair is a pullback in the category of presheaves. -/
theorem fiberProduct_spec {W : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w) :
    IsPullback (yoneda.map (fiberProductFst w hw))
      (yoneda.map (fiberProductSnd w hw)) w w := sorry

/-- The diagonal of a representable étale chart in its represented kernel pair. -/
noncomputable def diagonal {W : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w) :
    W ⟶ fiberProduct w hw :=
  yoneda.preimage (PullbackCone.IsLimit.lift (hw.rep.isPullback w).isLimit
    (𝟙 (yoneda.obj W)) (𝟙 (yoneda.obj W)) rfl)

/-- The diagonal is a section of the first kernel-pair projection. -/
theorem diagonal_fst {W : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w) :
    diagonal w hw ≫ fiberProductFst w hw = 𝟙 W := sorry

/-- The diagonal is a section of the second kernel-pair projection. -/
theorem diagonal_snd {W : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w) :
    diagonal w hw ≫ fiberProductSnd w hw = 𝟙 W := sorry

/-- The diagonal is an open immersion, being a section of an étale projection. -/
instance instIsOpenImmersionDiagonal {W : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w) :
    IsOpenImmersion (diagonal w hw) := sorry

/-- The scheme formed by gluing a represented kernel pair to `V` along `W`. -/
noncomputable def obj {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] : Scheme.{u} :=
  pushout (diagonal w hw) ιW

/-- The second kernel-pair projection agrees with the identity of `V` along `W`. -/
theorem source_condition {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] :
    diagonal w hw ≫ (fiberProductSnd w hw ≫ ιW) = ιW ≫ 𝟙 V := sorry

/-- The source projection extends the second kernel-pair projection and the identity of `V`. -/
noncomputable def source {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] : obj ιW w hw ⟶ V :=
  pushout.desc (fiberProductSnd w hw ≫ ιW) (𝟙 V) (source_condition ιW w hw)

/-- The first kernel-pair projection agrees with the identity of `V` along `W`. -/
theorem target_condition {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] :
    diagonal w hw ≫ (fiberProductFst w hw ≫ ιW) = ιW ≫ 𝟙 V := sorry

/-- The target projection extends the first kernel-pair projection and the identity of `V`. -/
noncomputable def target {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] : obj ιW w hw ⟶ V :=
  pushout.desc (fiberProductFst w hw ≫ ιW) (𝟙 V) (target_condition ιW w hw)

/-- The two kernel-pair projections have equal composites into the new base. -/
theorem fiberProductMap_condition {W W' : Scheme.{u}}
    {U U' : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    (w' : yoneda.obj W' ⟶ U') (hW : W ⟶ W') (u : U ⟶ U')
    (hWU : IsPullback (yoneda.map hW) w w' u) :
    yoneda.map (fiberProductFst w hw ≫ hW) ≫ w' =
      yoneda.map (fiberProductSnd w hw ≫ hW) ≫ w' := sorry

/-- The comparison of represented kernel pairs induced by a cartesian chart transition. -/
noncomputable def fiberProductMap {W W' : Scheme.{u}}
    {U U' : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    (w' : yoneda.obj W' ⟶ U') (hw' : MorphismProperty.presheaf (@Etale) w')
    (hW : W ⟶ W') (u : U ⟶ U') (hWU : IsPullback (yoneda.map hW) w w' u) :
    fiberProduct w hw ⟶ fiberProduct w' hw' :=
  yoneda.preimage (PullbackCone.IsLimit.lift (hw'.rep.isPullback w').isLimit
    (yoneda.map (fiberProductFst w hw ≫ hW)) (yoneda.map (fiberProductSnd w hw ≫ hW))
    (fiberProductMap_condition w hw w' hW u hWU))

/-- The diagonal commutes with comparison maps of represented kernel pairs. -/
theorem diagonal_natural {W W' : Scheme.{u}} {U U' : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    (w' : yoneda.obj W' ⟶ U') (hw' : MorphismProperty.presheaf (@Etale) w')
    (hW : W ⟶ W') (u : U ⟶ U') (hWU : IsPullback (yoneda.map hW) w w' u) :
    diagonal w hw ≫ fiberProductMap w hw w' hw' hW u hWU =
      hW ≫ diagonal w' hw' := sorry

/-- The transition of glued relations induced by cartesian chart and open-subscheme transitions. -/
noncomputable def map {W V W' V' : Scheme.{u}} {U U' : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    (ιW' : W' ⟶ V') (w' : yoneda.obj W' ⟶ U') (hw' : MorphismProperty.presheaf (@Etale) w')
    [IsOpenImmersion ιW] [IsOpenImmersion ιW']
    (hW : W ⟶ W') (v : V ⟶ V') (u : U ⟶ U')
    (hWU : IsPullback (yoneda.map hW) w w' u) (hWV : IsPullback ιW hW v ιW') :
    obj ιW w hw ⟶ obj ιW' w' hw' :=
  pushout.map (diagonal w hw) ιW (diagonal w' hw') ιW'
    (fiberProductMap w hw w' hw' hW u hWU) v hW
    (diagonal_natural w hw w' hw' hW u hWU) hWV.w

/-- On the kernel-pair chart, the source is the second projection followed by `W ⟶ V`. -/
theorem source_inl {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] :
    pushout.inl (diagonal w hw) ιW ≫ source ιW w hw = fiberProductSnd w hw ≫ ιW := sorry

/-- On the `V` chart, the source is the identity. -/
theorem source_inr {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] :
    pushout.inr (diagonal w hw) ιW ≫ source ιW w hw = 𝟙 V := sorry

/-- On the kernel-pair chart, the target is the first projection followed by `W ⟶ V`. -/
theorem target_inl {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] :
    pushout.inl (diagonal w hw) ιW ≫ target ιW w hw = fiberProductFst w hw ≫ ιW := sorry

/-- On the `V` chart, the target is the identity. -/
theorem target_inr {W V : Scheme.{u}} {U : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    [IsOpenImmersion ιW] :
    pushout.inr (diagonal w hw) ιW ≫ target ιW w hw = 𝟙 V := sorry

/-- The square of second kernel-pair projections for a cartesian chart transition is cartesian. -/
theorem fiberProduct_isPullback {W W' : Scheme.{u}} {U U' : Scheme.{u}ᵒᵖ ⥤ Type u}
    (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    (w' : yoneda.obj W' ⟶ U') (hw' : MorphismProperty.presheaf (@Etale) w')
    (hW : W ⟶ W') (u : U ⟶ U') (hWU : IsPullback (yoneda.map hW) w w' u) :
    IsPullback (fiberProductMap w hw w' hw' hW u hWU)
      (fiberProductSnd w hw) (fiberProductSnd w' hw') hW := sorry

/-- Cartesian transitions of charts and open subschemes induce a cartesian source square
of the glued relations. -/
theorem source_isPullback {W V W' V' : Scheme.{u}} {U U' : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    (ιW' : W' ⟶ V') (w' : yoneda.obj W' ⟶ U') (hw' : MorphismProperty.presheaf (@Etale) w')
    [IsOpenImmersion ιW] [IsOpenImmersion ιW']
    (hW : W ⟶ W') (v : V ⟶ V') (u : U ⟶ U')
    (hWU : IsPullback (yoneda.map hW) w w' u) (hWV : IsPullback ιW hW v ιW') :
    IsPullback (map ιW w hw ιW' w' hw' hW v u hWU hWV)
      (source ιW w hw) (source ιW' w' hw') v := sorry

end AlgebraicGeometry.Scheme.PreRelation.ExtendOpen
