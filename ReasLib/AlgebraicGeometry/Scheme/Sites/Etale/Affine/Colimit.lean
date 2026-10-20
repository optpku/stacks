/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine.Pullback
public import ReasLib.CategoryTheory.Sites.Cofiltered.ColimitTopology

/-!
# Affine etale sites in directed inverse systems

This file constructs the affine etale base-change functors and the resulting
explicit cofiltered site diagram for an inverse system with affine transition
morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.AffineEtaleColimit

variable {S T : Scheme.{u}}

/-- Affine etale base change preserves the selected finite covering families. -/
theorem baseChange_isContinuous (f : T ⟶ S) [IsAffineHom f] :
    Functor.Precoverage.IsContinuous (AffineEtale.pullback f)
      (smallAffineEtalePrecoverage S) (smallAffineEtalePrecoverage T) := sorry

/-- Affine etale base change along an affine morphism is representably flat. -/
theorem baseChange_representablyFlat (f : T ⟶ S) [IsAffineHom f] :
    RepresentablyFlat (AffineEtale.pullback f) := sorry

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [hD : ∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))]

/-- The transition functor between affine etale sites associated to a morphism
in the opposite directed index category. -/
noncomputable def stageMap {i j : (OrderDual I)ᵒᵖ} (a : i ⟶ j) :
    (D.obj i.unop).AffineEtale ⥤ (D.obj j.unop).AffineEtale :=
  @AffineEtale.pullback _ _ (D.map a.unop) (hD (leOfHom a.unop))

/-- The affine etale transition attached to an identity arrow is the identity
functor in `Cat`. -/
theorem stageMap_id (i : (OrderDual I)ᵒᵖ) :
    (stageMap D (𝟙 i)).toCatHom = 𝟙 (Cat.of (D.obj i.unop).AffineEtale) := sorry

/-- Affine etale transition functors compose as the arrows of the index
category compose. -/
theorem stageMap_comp {i j k : (OrderDual I)ᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (stageMap D (a ≫ b)).toCatHom =
      (stageMap D a).toCatHom ≫ (stageMap D b).toCatHom := sorry

/-- The `Cat`-valued diagram of affine etale sites of the stages. -/
noncomputable def stageDiagram : (OrderDual I)ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj i := Cat.of (D.obj i.unop).AffineEtale
  map a := (stageMap D a).toCatHom
  map_id := stageMap_id D
  map_comp := stageMap_comp D

/-- Every selected affine etale covering family is finite. -/
theorem precoverage_finite (S : Scheme.{u}) {U : S.AffineEtale} {R : Presieve U} :
    R ∈ smallAffineEtalePrecoverage S U →
      R ∈ Precoverage.finite S.AffineEtale U := sorry

/-- The selected finite affine etale precoverage contains singleton
isomorphisms. -/
theorem precoverage_hasIsos (S : Scheme.{u}) :
    (smallAffineEtalePrecoverage S).HasIsos := sorry

/-- Members of selected finite affine etale covers admit pullbacks. -/
theorem precoverage_hasPullbacks (S : Scheme.{u}) :
    (smallAffineEtalePrecoverage S).HasPullbacks := sorry

/-- Selected finite affine etale covers are stable under arrowwise
refinement. -/
theorem precoverage_isStableUnderBind (S : Scheme.{u}) :
    (smallAffineEtalePrecoverage S).IsStableUnderBind := sorry

/-- Selected finite affine etale covers are stable under chosen pullback
families. -/
theorem precoverage_isStableUnderPullbackArrows (S : Scheme.{u}) :
    (smallAffineEtalePrecoverage S).IsStableUnderPullbackArrows := sorry

/-- The explicit cofiltered site diagram formed by the affine etale sites of
an affine-transition inverse system of schemes. -/
noncomputable def diagram [Nonempty I] [IsDirected I (· ≤ ·)] :
    CofilteredSiteDiagram.{u, u + 1, u} where
  I := OrderDual I
  smallCategoryI := inferInstance
  cofilteredI := inferInstance
  diagram := stageDiagram D
  stageCov i := smallAffineEtalePrecoverage (D.obj i)
  stageCov_finite := precoverage_finite _
  stageCov_hasIsos i := precoverage_hasIsos (D.obj i)
  stageCov_hasPullbacks i := precoverage_hasPullbacks (D.obj i)
  stageCov_isStableUnderBind i := precoverage_isStableUnderBind (D.obj i)
  stageCov_isStableUnderPullbackArrows i :=
    precoverage_isStableUnderPullbackArrows (D.obj i)
  transitionContinuous a :=
    @baseChange_isContinuous _ _ (D.map a) (hD (leOfHom a))
  transition_representablyFlat a :=
    @baseChange_representablyFlat _ _ (D.map a) (hD (leOfHom a))

/-- The category at a stage of `diagram D` is that stage's affine etale
category. -/
theorem diagram_obj [Nonempty I] [IsDirected I (· ≤ ·)] (i : OrderDual I) :
    (diagram D).stage i = (D.obj i).AffineEtale := sorry

/-- The selected covering families at a stage of `diagram D` are the finite
affine etale covering families. -/
theorem diagram_precoverage [Nonempty I] [IsDirected I (· ≤ ·)] (i : OrderDual I) :
    (diagram D).stageCov i = smallAffineEtalePrecoverage (D.obj i) := sorry

/-- The affine etale site of a limit is the colimit site of an affine-transition
inverse system. -/
theorem isColimitSite {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))]
    (c : Cone D) (hc : IsLimit c) :
    ∃ e : (diagram D).ColimitCategory ≌ c.pt.AffineEtale,
      e.functor.inducedTopology (Scheme.AffineEtale.topology c.pt) =
        (diagram D).colimitTopology := sorry

end AlgebraicGeometry.Scheme.AffineEtaleColimit
