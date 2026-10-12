/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over.BaseChange
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange.Composition
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FlatProjection

/-!
# Continuity diagrams for cycles and Chow groups

This module constructs the canonical directed diagrams, cocones, and comparison
morphisms associated to a compatible inverse system of base schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowLimit

variable {I : Type u} [Preorder I]
variable {S : Scheme.{u}} [hS_catenary : UniversallyCatenary S]
variable (D : OrderDual I ⥤ Scheme.{u})
variable (t : D ⟶ (Functor.const (OrderDual I)).obj S)
variable (δ : S → ℤ) [hδ : IsDimensionFunction δ]

/-- The structure morphism from a stage of the inverse system to `S`. -/
abbrev stageMap (i : I) : D.obj (OrderDual.toDual i) ⟶ S :=
  t.app (OrderDual.toDual i)

/-- The stage structure morphism is the corresponding component of the system map. -/
theorem stageMap_eq_app (i : I) :
    stageMap D t i = t.app (OrderDual.toDual i) := sorry

/-- The dimension function on a stage is the composite of its structure map with the
dimension function on the base. -/
def stageDimension (i : I) : D.obj (OrderDual.toDual i) → ℤ :=
  fun x ↦ δ (stageMap D t i x)

/-- Evaluation of the dimension function induced on a stage. -/
theorem stageDimension_apply (i : I) (x : D.obj (OrderDual.toDual i)) :
    stageDimension D t δ i x = δ (stageMap D t i x) := sorry

/-- The base change of an `S`-scheme to the stage indexed by `i`. -/
noncomputable abbrev stageBaseChange (X : Over S) (i : I) :
    Over (D.obj (OrderDual.toDual i)) :=
  (Over.pullback (stageMap D t i)).obj X

/-- The underlying scheme of `stageBaseChange` is the canonical pullback scheme. -/
theorem stageBaseChange_left (X : Over S) (i : I) :
    (stageBaseChange D t X i).left = pullback X.hom (stageMap D t i) := sorry

/-- The base change of an `S`-scheme to the limiting scheme. -/
noncomputable abbrev limitBaseChange {S' : Scheme.{u}} (g : S' ⟶ S) (X : Over S) : Over S' :=
  (Over.pullback g).obj X

/-- The underlying scheme of `limitBaseChange` is the canonical pullback scheme. -/
theorem limitBaseChange_left {S' : Scheme.{u}} (g : S' ⟶ S) (X : Over S) :
    (limitBaseChange g X).left = pullback X.hom g := sorry

variable [hD_catenary : ∀ i : OrderDual I, UniversallyCatenary (D.obj i)]
variable [hD_dimension : ∀ i : I, IsDimensionFunction (stageDimension D t δ i)]
variable [hstage_flat : ∀ i : I, Flat (stageMap D t i)]
variable (X : Over S) [hX_finite : Scheme.Hom.FiniteType X.hom]
variable (k : ℤ)

/-- The cycle group at a stage of the inverse system. -/
abbrev cycleObject (i : I) : AddCommGrpCat :=
  AddCommGrpCat.of (CycleGroup (stageBaseChange D t X i).left
    ((stageBaseChange D t X i).hom.relativeDimensionFunction (stageDimension D t δ i)) k)

/-- The Chow group at a stage of the inverse system. -/
abbrev chowObject (i : I) : AddCommGrpCat :=
  AddCommGrpCat.of (@ChowGroup (stageBaseChange D t X i).left
    (LocallyOfFiniteType.isLocallyNoetherian (stageBaseChange D t X i).hom)
    ((stageBaseChange D t X i).hom.relativeDimensionFunction (stageDimension D t δ i))
    inferInstance k)

variable [htransition_flat : ∀ (i j : I) (h : i ≤ j), Flat (D.map (homOfLE h))]
variable (htransition : ∀ (i j : I) (h : i ≤ j),
  @Scheme.Hom.IsDimensionFunctionCompatible
    (D.obj (OrderDual.toDual i)) (D.obj (OrderDual.toDual j))
    (hD_catenary _) (hD_catenary _) (D.map (homOfLE h)) (htransition_flat i j h)
    (stageDimension D t δ i) (hD_dimension i)
    (stageDimension D t δ j) (hD_dimension j) 0)

/-- The zero-shift flat pullback map on cycle groups from stage `i` to stage `j`. -/
noncomputable def cycleTransition {i j : I} (h : i ≤ j) :
    cycleObject D t δ X k i ⟶ cycleObject D t δ X k j :=
  AddCommGrpCat.ofHom
      ((@CycleGroup.iteratedBaseChangeMap S (D.obj (OrderDual.toDual i))
        (D.obj (OrderDual.toDual j)) X.left (hD_catenary _)
        X.hom inferInstance (stageMap D t i) (D.map (homOfLE h))
        (stageDimension D t δ j) (hD_dimension j) (k + 0) k (add_zero k)).comp
        (@CycleGroup.baseChangePullback (D.obj (OrderDual.toDual i))
          (D.obj (OrderDual.toDual j)) (stageBaseChange D t X i).left
          (hD_catenary _) (hD_catenary _) (D.map (homOfLE h)) (htransition_flat i j h)
          (stageDimension D t δ i) (hD_dimension i)
          (stageDimension D t δ j) (hD_dimension j) 0
          (htransition i j h) (stageBaseChange D t X i).hom inferInstance k)) ≫
    eqToHom (congrArg (fun q : D.obj (OrderDual.toDual j) ⟶ S ↦
      AddCommGrpCat.of (CycleGroup (pullback X.hom q)
        ((pullback.snd X.hom q).relativeDimensionFunction (stageDimension D t δ j)) k))
      ((t.naturality (homOfLE h)).trans (Category.comp_id _)))

/-- The cycle transition along an identity arrow is the identity morphism. -/
theorem cycleTransition_id (i : I) :
    cycleTransition D t δ X k htransition (le_refl i) = 𝟙 _ := sorry

/-- Cycle transitions compose along comparable stages. -/
theorem cycleTransition_comp {i j l : I} (hij : i ≤ j) (hjl : j ≤ l) :
    cycleTransition D t δ X k htransition hij ≫
      cycleTransition D t δ X k htransition hjl =
        cycleTransition D t δ X k htransition (hij.trans hjl) := sorry

/-- The directed diagram of degree-`k` cycle groups of the stagewise base changes. -/
noncomputable def cycleDiagram : I ⥤ AddCommGrpCat where
  obj i := cycleObject D t δ X k i
  map f := cycleTransition D t δ X k htransition (leOfHom f)
  map_id i := cycleTransition_id D t δ X k htransition i
  map_comp f g := (cycleTransition_comp D t δ X k htransition
    (leOfHom f) (leOfHom g)).symm

/-- The objects of `cycleDiagram` are the degree-`k` cycle groups of the stagewise
base changes. -/
theorem cycleDiagram_obj (i : I) :
    (cycleDiagram D t δ X k htransition).obj i = cycleObject D t δ X k i := sorry

/-- The maps of `cycleDiagram` are the canonical flat base-change transitions. -/
theorem cycleDiagram_map {i j : I} (h : i ≤ j) :
    (cycleDiagram D t δ X k htransition).map (homOfLE h) =
      cycleTransition D t δ X k htransition h := sorry

/-- The zero-shift flat pullback map on Chow groups from stage `i` to stage `j`. -/
noncomputable def chowTransition {i j : I} (h : i ≤ j) :
    chowObject D t δ X k i ⟶ chowObject D t δ X k j :=
  AddCommGrpCat.ofHom
      ((@ChowGroup.iteratedBaseChangeMap S (D.obj (OrderDual.toDual i))
        (D.obj (OrderDual.toDual j)) X.left (hD_catenary _)
        X.hom inferInstance (stageMap D t i) (D.map (homOfLE h))
        (stageDimension D t δ j) (hD_dimension j) (k + 0) k (add_zero k)).comp
        (@ChowGroup.baseChangePullback (D.obj (OrderDual.toDual i))
          (D.obj (OrderDual.toDual j)) (stageBaseChange D t X i).left
          (hD_catenary _) (hD_catenary _) (D.map (homOfLE h)) (htransition_flat i j h)
          (stageDimension D t δ i) (hD_dimension i)
          (stageDimension D t δ j) (hD_dimension j) 0
          (htransition i j h) (stageBaseChange D t X i).hom inferInstance k)) ≫
    eqToHom (congrArg (fun q : D.obj (OrderDual.toDual j) ⟶ S ↦
      AddCommGrpCat.of (@ChowGroup (pullback X.hom q)
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd X.hom q))
        ((pullback.snd X.hom q).relativeDimensionFunction (stageDimension D t δ j))
        inferInstance k))
      ((t.naturality (homOfLE h)).trans (Category.comp_id _)))

/-- The Chow transition along an identity arrow is the identity morphism. -/
theorem chowTransition_id (i : I) :
    chowTransition D t δ X k htransition (le_refl i) = 𝟙 _ := sorry

/-- Chow transitions compose along comparable stages. -/
theorem chowTransition_comp {i j l : I} (hij : i ≤ j) (hjl : j ≤ l) :
    chowTransition D t δ X k htransition hij ≫
      chowTransition D t δ X k htransition hjl =
        chowTransition D t δ X k htransition (hij.trans hjl) := sorry

/-- The directed diagram of degree-`k` Chow groups of the stagewise base changes. -/
noncomputable def chowDiagram : I ⥤ AddCommGrpCat where
  obj i := chowObject D t δ X k i
  map f := chowTransition D t δ X k htransition (leOfHom f)
  map_id i := chowTransition_id D t δ X k htransition i
  map_comp f g := (chowTransition_comp D t δ X k htransition
    (leOfHom f) (leOfHom g)).symm

/-- The objects of `chowDiagram` are the degree-`k` Chow groups of the stagewise
base changes. -/
theorem chowDiagram_obj (i : I) :
    (chowDiagram D t δ X k htransition).obj i = chowObject D t δ X k i := sorry

/-- The maps of `chowDiagram` are the canonical flat base-change transitions. -/
theorem chowDiagram_map {i j : I} (h : i ≤ j) :
    (chowDiagram D t δ X k htransition).map (homOfLE h) =
      chowTransition D t δ X k htransition h := sorry

variable (c : Cone D) (g : c.pt ⟶ S) [hc_catenary : UniversallyCatenary c.pt]
variable [hg_flat : Flat g]
variable (δ' : c.pt → ℤ) [hδ' : IsDimensionFunction δ']
variable (hπ : c.π ≫ t = (Functor.const (OrderDual I)).map g)

/-- The morphism from the limiting scheme to a stage. -/
abbrev coneMap (i : I) : c.pt ⟶ D.obj (OrderDual.toDual i) :=
  c.π.app (OrderDual.toDual i)

/-- The cone map is the corresponding component of the limiting cone. -/
theorem coneMap_eq_app (i : I) : coneMap D c i = c.π.app (OrderDual.toDual i) := sorry

section CompatibleLegs

variable [hleg_flat : ∀ i : I, Flat (coneMap D c i)]
variable (hleg : ∀ i : I,
  @Scheme.Hom.IsDimensionFunctionCompatible (D.obj (OrderDual.toDual i)) c.pt
    (hD_catenary _) hc_catenary (coneMap D c i) (hleg_flat i)
    (stageDimension D t δ i) (hD_dimension i) δ' hδ' 0)

/-- The canonical map from a stage cycle group to the cycle group on the limiting base
change. -/
noncomputable def cycleLeg (i : I) :
    cycleObject D t δ X k i ⟶
      AddCommGrpCat.of (CycleGroup (limitBaseChange g X).left
        ((limitBaseChange g X).hom.relativeDimensionFunction δ') k) :=
  AddCommGrpCat.ofHom
      ((@CycleGroup.iteratedBaseChangeMap S (D.obj (OrderDual.toDual i)) c.pt X.left
        hc_catenary X.hom inferInstance (stageMap D t i) (coneMap D c i)
        δ' hδ' (k + 0) k (add_zero k)).comp
        (@CycleGroup.baseChangePullback (D.obj (OrderDual.toDual i)) c.pt
          (stageBaseChange D t X i).left (hD_catenary _) hc_catenary
          (coneMap D c i) (hleg_flat i) (stageDimension D t δ i) (hD_dimension i)
          δ' hδ' 0 (hleg i) (stageBaseChange D t X i).hom inferInstance k)) ≫
    eqToHom (congrArg (fun q : c.pt ⟶ S ↦
      AddCommGrpCat.of (CycleGroup (pullback X.hom q)
        ((pullback.snd X.hom q).relativeDimensionFunction δ') k))
      ((congrArg (fun η ↦ η.app (OrderDual.toDual i)) hπ).trans (Category.id_comp g)))

/-- Cycle transition maps commute with the canonical maps to the limiting base change. -/
theorem cycleLeg_naturality {i j : I} (h : i ≤ j) :
    cycleTransition D t δ X k htransition h ≫ cycleLeg D t δ X k c g δ' hπ hleg j =
      cycleLeg D t δ X k c g δ' hπ hleg i := sorry

/-- The canonical cocone from the stage cycle groups to cycles on the limiting base change. -/
noncomputable def cycleCocone : Cocone (cycleDiagram D t δ X k htransition) where
  pt := AddCommGrpCat.of (CycleGroup (limitBaseChange g X).left
    ((limitBaseChange g X).hom.relativeDimensionFunction δ') k)
  ι :=
    { app := cycleLeg D t δ X k c g δ' hπ hleg
      naturality := fun _ _ f ↦ cycleLeg_naturality D t δ X k htransition c g δ' hπ hleg (leOfHom f) }

/-- A component of the cycle cocone is the canonical cycle pullback to the limit. -/
theorem cycleCocone_ι_app (i : I) :
    (cycleCocone D t δ X k htransition c g δ' hπ hleg).ι.app i =
      cycleLeg D t δ X k c g δ' hπ hleg i := sorry

/-- The canonical comparison from the colimit of stage cycle groups to cycles on the
limiting base change. -/
noncomputable def cycleComparison :
    colimit (cycleDiagram D t δ X k htransition) ⟶
      (cycleCocone D t δ X k htransition c g δ' hπ hleg).pt :=
  colimit.desc (cycleDiagram D t δ X k htransition)
    (cycleCocone D t δ X k htransition c g δ' hπ hleg)

/-- The cycle comparison restricts at every stage to the canonical cocone leg. -/
theorem colimit_ι_cycleComparison (i : I) :
    colimit.ι (cycleDiagram D t δ X k htransition) i ≫
      cycleComparison D t δ X k htransition c g δ' hπ hleg =
        cycleLeg D t δ X k c g δ' hπ hleg i := sorry

/-- The canonical map from a stage Chow group to the Chow group on the limiting base
change. -/
noncomputable def chowLeg (i : I) :
    chowObject D t δ X k i ⟶
      AddCommGrpCat.of (@ChowGroup (limitBaseChange g X).left
        (LocallyOfFiniteType.isLocallyNoetherian (limitBaseChange g X).hom)
        ((limitBaseChange g X).hom.relativeDimensionFunction δ') inferInstance k) :=
  AddCommGrpCat.ofHom
      ((@ChowGroup.iteratedBaseChangeMap S (D.obj (OrderDual.toDual i)) c.pt X.left
        hc_catenary X.hom inferInstance (stageMap D t i) (coneMap D c i)
        δ' hδ' (k + 0) k (add_zero k)).comp
        (@ChowGroup.baseChangePullback (D.obj (OrderDual.toDual i)) c.pt
          (stageBaseChange D t X i).left (hD_catenary _) hc_catenary
          (coneMap D c i) (hleg_flat i) (stageDimension D t δ i) (hD_dimension i)
          δ' hδ' 0 (hleg i) (stageBaseChange D t X i).hom inferInstance k)) ≫
    eqToHom (congrArg (fun q : c.pt ⟶ S ↦
      AddCommGrpCat.of (@ChowGroup (pullback X.hom q)
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd X.hom q))
        ((pullback.snd X.hom q).relativeDimensionFunction δ') inferInstance k))
      ((congrArg (fun η ↦ η.app (OrderDual.toDual i)) hπ).trans (Category.id_comp g)))

/-- Chow transition maps commute with the canonical maps to the limiting base change. -/
theorem chowLeg_naturality {i j : I} (h : i ≤ j) :
    chowTransition D t δ X k htransition h ≫ chowLeg D t δ X k c g δ' hπ hleg j =
      chowLeg D t δ X k c g δ' hπ hleg i := sorry

/-- The canonical cocone from the stage Chow groups to the Chow group on the limiting base
change. -/
noncomputable def chowCocone : Cocone (chowDiagram D t δ X k htransition) where
  pt := AddCommGrpCat.of (@ChowGroup (limitBaseChange g X).left
    (LocallyOfFiniteType.isLocallyNoetherian (limitBaseChange g X).hom)
    ((limitBaseChange g X).hom.relativeDimensionFunction δ') inferInstance k)
  ι :=
    { app := chowLeg D t δ X k c g δ' hπ hleg
      naturality := fun _ _ f ↦ chowLeg_naturality D t δ X k htransition c g δ' hπ hleg (leOfHom f) }

/-- A component of the Chow cocone is the canonical Chow pullback to the limit. -/
theorem chowCocone_ι_app (i : I) :
    (chowCocone D t δ X k htransition c g δ' hπ hleg).ι.app i =
      chowLeg D t δ X k c g δ' hπ hleg i := sorry

/-- The canonical comparison from the colimit of stage Chow groups to the Chow group on the
limiting base change. -/
noncomputable def chowComparison :
    colimit (chowDiagram D t δ X k htransition) ⟶
      (chowCocone D t δ X k htransition c g δ' hπ hleg).pt :=
  colimit.desc (chowDiagram D t δ X k htransition)
    (chowCocone D t δ X k htransition c g δ' hπ hleg)

/-- The Chow comparison restricts at every stage to the canonical cocone leg. -/
theorem colimit_ι_chowComparison (i : I) :
    colimit.ι (chowDiagram D t δ X k htransition) i ≫
      chowComparison D t δ X k htransition c g δ' hπ hleg =
        chowLeg D t δ X k c g δ' hπ hleg i := sorry

end CompatibleLegs

variable [hI_nonempty : Nonempty I] [hI_directed : IsDirected I (· ≤ ·)]
variable (hc : IsLimit c)
variable [hD_affine : ∀ i : I, IsAffineHom (stageMap D t i)]
variable (hcompat : g.IsDimensionFunctionCompatible δ δ' 0)
variable (hstage : ∀ i : I,
  @Scheme.Hom.IsDimensionFunctionCompatible S (D.obj (OrderDual.toDual i))
    hS_catenary (hD_catenary _) (stageMap D t i) (hstage_flat i)
    δ hδ (stageDimension D t δ i) (hD_dimension i) 0)

/-- The cycle cocone of a directed affine limit, with flat compatible projections derived
from the limiting cone and the dimension functions on its base and stages. -/
noncomputable def limitCycleCocone : Cocone (cycleDiagram D t δ X k htransition) :=
  cycleCocone D t δ X k htransition c g δ' hπ
    (hleg_flat := fun index ↦ Scheme.Limit.flatProjection D t c hc
      (hD_affine := hD_affine) index)
    (fun index ↦ Scheme.Limit.projectionDimension_eq D t c hc g hπ δ δ'
      (hD_affine := hD_affine) (hD_dimension := hD_dimension) (hstage_flat := hstage_flat)
      hcompat hstage htransition index)

/-- The Chow cocone of a directed affine limit, with flat compatible projections derived
from the limiting cone and the dimension functions on its base and stages. -/
noncomputable def limitChowCocone : Cocone (chowDiagram D t δ X k htransition) :=
  chowCocone D t δ X k htransition c g δ' hπ
    (hleg_flat := fun index ↦ Scheme.Limit.flatProjection D t c hc
      (hD_affine := hD_affine) index)
    (fun index ↦ Scheme.Limit.projectionDimension_eq D t c hc g hπ δ δ'
      (hD_affine := hD_affine) (hD_dimension := hD_dimension) (hstage_flat := hstage_flat)
      hcompat hstage htransition index)

/-- The morphism from the colimit of stage cycle groups to the cycle group of a limiting
base change, induced by its canonical cocone. -/
noncomputable def limitCycleComparison :
    colimit (cycleDiagram D t δ X k htransition) ⟶
      (limitCycleCocone D t δ X k htransition c g δ' hπ hc hcompat hstage).pt :=
  colimit.desc (cycleDiagram D t δ X k htransition)
    (limitCycleCocone D t δ X k htransition c g δ' hπ hc hcompat hstage)

/-- The morphism from the colimit of stage Chow groups to the Chow group of a limiting
base change, induced by its canonical cocone. -/
noncomputable def limitChowComparison :
    colimit (chowDiagram D t δ X k htransition) ⟶
      (limitChowCocone D t δ X k htransition c g δ' hπ hc hcompat hstage).pt :=
  colimit.desc (chowDiagram D t δ X k htransition)
    (limitChowCocone D t δ X k htransition c g δ' hπ hc hcompat hstage)

variable [hX_compact : CompactSpace X.left]

include hX_compact

/-- Cycles of a quasi-compact finite-type scheme after a directed affine limiting base
change are the colimit of the stage cycle groups under zero-shift flat pullback. -/
theorem cycleCocone_isColimit : Nonempty (IsColimit
    (limitCycleCocone D t δ X k htransition c g δ' hπ hc hcompat hstage)) := sorry

/-- Chow groups of a quasi-compact finite-type scheme after a directed affine limiting
base change are the colimit of the stage Chow groups under zero-shift flat pullback. -/
theorem chowCocone_isColimit : Nonempty (IsColimit
    (limitChowCocone D t δ X k htransition c g δ' hπ hc hcompat hstage)) := sorry

/-- The canonical comparison from the colimit of stage cycle groups to cycles on the
limiting base change of a quasi-compact finite-type scheme is an isomorphism. -/
instance cycleComparison_isIso :
    IsIso (limitCycleComparison D t δ X k htransition c g δ' hπ hc hcompat hstage) := sorry

/-- The canonical comparison from the colimit of stage Chow groups to the Chow group on
the limiting base change of a quasi-compact finite-type scheme is an isomorphism. -/
instance chowComparison_isIso :
    IsIso (limitChowComparison D t δ X k htransition c g δ' hπ hc hcompat hstage) := sorry

end AlgebraicGeometry.ChowLimit
