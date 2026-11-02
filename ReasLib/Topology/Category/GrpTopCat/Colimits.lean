/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Topology.Algebra.Group.GroupTopology
public import Mathlib.Topology.Category.TopCat.Adjunctions
public import ReasLib.Topology.Category.GrpTopCat.Concrete

/-!
# Colimits of topological group objects
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj

namespace GrpTopCat

instance isTopologicalGroup (X : Grp TopCat.{u}) : IsTopologicalGroup X.X where
  continuous_mul := (TopCat.Hom.hom μ[X.X]).continuous
  continuous_inv := (TopCat.Hom.hom ι[X.X]).continuous

/-- Realize a topological group as an internal group object, using its given operations. -/
def ofTopologicalGroup (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Grp TopCat.{u} where
  X := TopCat.of G
  grp :=
    { one := TopCat.ofHom ⟨fun _ => 1, continuous_const⟩
      mul := TopCat.ofHom ⟨fun p => p.1 * p.2, continuous_mul⟩
      inv := TopCat.ofHom ⟨fun x => x⁻¹, continuous_inv⟩
      one_mul := by
        apply TopCat.ext
        intro x
        exact _root_.one_mul x.2
      mul_one := by
        apply TopCat.ext
        intro x
        exact _root_.mul_one x.1
      mul_assoc := by
        apply TopCat.ext
        intro x
        exact _root_.mul_assoc x.1.1 x.1.2 x.2
      left_inv := by
        apply TopCat.ext
        intro x
        exact inv_mul_cancel x
      right_inv := by
        apply TopCat.ext
        intro x
        exact mul_inv_cancel x }

namespace ColimitConstruction

variable {J : Type u} [Category.{u} J] (F : J ⥤ Grp TopCat.{u})

/-- The group laws in each vertex and the identifications imposed by arrows of the diagram. -/
inductive Relation : FreeGroup (Σ j, (F.obj j).X) → Prop
  | unit (j : J) : Relation (FreeGroup.of ⟨j, 1⟩)
  | mul (j : J) (x y : (F.obj j).X) : Relation
      (FreeGroup.of ⟨j, x * y⟩ * (FreeGroup.of ⟨j, x⟩ * FreeGroup.of ⟨j, y⟩)⁻¹)
  | map {i j : J} (f : i ⟶ j) (x : (F.obj i).X) : Relation
      (FreeGroup.of ⟨j, homToContinuousMonoidHom (F.map f) x⟩ * (FreeGroup.of ⟨i, x⟩)⁻¹)

/-- The algebraic colimit, presented by the elements of all vertices and their relations. -/
abbrev Carrier := PresentedGroup (Relation F)

/-- The canonical homomorphism from a vertex to the presented group. -/
def inclusion (j : J) : (F.obj j).X →* Carrier F where
  toFun x := PresentedGroup.of ⟨j, x⟩
  map_one' := PresentedGroup.one_of_mem (Relation.unit j)
  map_mul' x y := by
    simpa only [PresentedGroup.of, map_mul] using
      (PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relation.mul j x y))

theorem inclusion_map {i j : J} (f : i ⟶ j) (x : (F.obj i).X) :
    inclusion F j (homToContinuousMonoidHom (F.map f) x) = inclusion F i x :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relation.map f x)

variable {G : Type u} [Group G]

/-- Extend a compatible family by the universal property of the explicit group presentation. -/
def lift (f : ∀ j, (F.obj j).X →* G)
    (hf : ∀ {i j : J} (g : i ⟶ j) (x : (F.obj i).X),
      f j (homToContinuousMonoidHom (F.map g) x) = f i x) : Carrier F →* G :=
  PresentedGroup.toGroup (f := fun x => f x.1 x.2) (by
    intro r hr
    cases hr with
    | unit j => simp
    | mul j x y => simp
    | map g x =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hf g x, mul_inv_cancel])

@[simp]
theorem lift_inclusion (f : ∀ j, (F.obj j).X →* G)
    (hf : ∀ {i j : J} (g : i ⟶ j) (x : (F.obj i).X),
      f j (homToContinuousMonoidHom (F.map g) x) = f i x) (j : J) (x : (F.obj j).X) :
    lift F f hf (inclusion F j x) = f j x :=
  PresentedGroup.toGroup.of _

theorem inclusion_hom_ext {f g : Carrier F →* G}
    (h : ∀ j x, f (inclusion F j x) = g (inclusion F j x)) : f = g := by
  apply PresentedGroup.ext
  rintro ⟨j, x⟩
  exact h j x

/-- The finest group topology making all vertex homomorphisms continuous. -/
def topology : GroupTopology (Carrier F) :=
  GroupTopology.coinduced (fun x : Σ j, (F.obj j).X => inclusion F x.1 x.2)

-- These instances fix the topology only for this explicit construction.
local instance carrierTopology : TopologicalSpace (Carrier F) :=
  (topology F).toTopologicalSpace

local instance carrierTopologicalGroup : IsTopologicalGroup (Carrier F) :=
  (topology F).toIsTopologicalGroup

/-- The topological group underlying the explicit colimit cocone. -/
def point : Grp TopCat.{u} := ofTopologicalGroup (Carrier F)

theorem continuous_inclusion (j : J) : Continuous (inclusion F j) :=
  (GroupTopology.coinduced_continuous
    (fun x : Σ j, (F.obj j).X => inclusion F x.1 x.2)).comp continuous_sigmaMk

/-- The explicit cocone, with the vertex maps given by the generators of the presentation. -/
def cocone : Cocone F where
  pt := point F
  «ι» :=
    { app j := ConcreteCategory.ofHom (C := Grp TopCat)
        { inclusion F j with continuous_toFun := continuous_inclusion F j }
      naturality {i j} f := by
        apply Grp.hom_ext
        apply TopCat.ext
        intro x
        exact inclusion_map F f x }

/-- The algebraic descent map associated to a cocone of topological groups. -/
def descHom (s : Cocone F) : Carrier F →* s.pt.X :=
  lift F (fun j => (homToContinuousMonoidHom (s.ι.app j)).toMonoidHom) (by
    intro i j f x
    exact ConcreteCategory.congr_hom (s.w f) x)

@[simp]
theorem descHom_inclusion (s : Cocone F) (j : J) (x : (F.obj j).X) :
    descHom F s (inclusion F j x) = homToContinuousMonoidHom (s.ι.app j) x := by
  dsimp only [descHom, lift, inclusion]
  exact PresentedGroup.toGroup.of _

theorem continuous_descHom (s : Cocone F) : Continuous (descHom F s) := by
  let t : GroupTopology (Carrier F) :=
    { toTopologicalSpace := TopologicalSpace.induced (descHom F s) s.pt.X.str
      toIsTopologicalGroup := topologicalGroup_induced (descHom F s) }
  apply continuous_iff_le_induced.mpr
  change (topology F).toTopologicalSpace ≤ t.toTopologicalSpace
  apply GroupTopology.toTopologicalSpace_le.mpr
  apply sInf_le
  change TopologicalSpace.coinduced _ _ ≤ _
  apply continuous_iff_coinduced_le.mp
  apply continuous_induced_rng.mpr
  apply continuous_sigma
  intro j
  change Continuous (fun x => descHom F s (inclusion F j x))
  have h : (fun x => descHom F s (inclusion F j x)) =
      (fun x => homToContinuousMonoidHom (s.ι.app j) x) := by
    funext x
    exact descHom_inclusion F s j x
  rw [h]
  exact (homToContinuousMonoidHom (s.ι.app j)).continuous

/-- The cocone has the universal property, with an explicitly defined descent map. -/
def isColimit : IsColimit (cocone F) where
  desc s := ConcreteCategory.ofHom (C := Grp TopCat)
    { descHom F s with continuous_toFun := continuous_descHom F s }
  fac s j := by
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    exact descHom_inclusion F s j x
  uniq s m hm := by
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    have h : (homToContinuousMonoidHom m).toMonoidHom = descHom F s := by
      apply inclusion_hom_ext F
      intro j y
      exact (ConcreteCategory.congr_hom (hm j) y).trans (descHom_inclusion F s j y).symm
    exact DFunLike.congr_fun h x

end ColimitConstruction

/-- The category of topological group objects has all small colimits. -/
@[stacks 0B21 "topological groups have colimits"]
instance hasColimits : HasColimits (Grp TopCat.{u}) where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F => HasColimit.mk
        { cocone := ColimitConstruction.cocone F
          isColimit := ColimitConstruction.isColimit F } }

/-- Forgetting a topological group object to its ordinary group preserves all small colimits. -/
@[stacks 0B21 "colimits commute with the forgetful functor to groups"]
instance forgetToGrpCat_preservesColimits :
    PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) := by
  -- Match the local finite-product presentation used to define `forget₂` in `Concrete`.
  letI : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  letI : TopCat.trivial.{u}.IsRightAdjoint := ⟨_, ⟨TopCat.adj₂⟩⟩
  letI : TopCat.trivial.{u}.Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts TopCat.trivial.{u}
  exact (TopCat.adj₂.mapGrp.comp grpTypeEquivalenceGrp.toAdjunction).leftAdjoint_preservesColimits

end GrpTopCat
