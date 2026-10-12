/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Topology.Category.TopCat.Opens
public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Definition
public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.ULift

/-!
# Simplicial topological spaces from simplicial families of opens

This module turns any simplicial family of opens into its degreewise disjoint-union simplicial
topological space, together with its canonical augmentation to the base space.  The construction
does not use the covering conditions imposed on an open hypercovering.  The index simplicial set
may live in any universe dominated by the universe of the resulting topological spaces.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u v

namespace SSet
namespace OpenFamily

variable {X : TopCat.{max u v}} {I : SSet.{v}} (U : OpenFamily X I)

/-- The degree-`n` disjoint-union topological space associated to a simplicial family of opens. -/
@[stacks 02N9 "degreewise space of a simplicial family of opens"]
abbrev simplicialSpace.degree.obj (n : ℕ) : TopCat.{max u v} :=
  TopCat.of (Σ i : I.obj (op <| SimplexCategory.mk n), U.openAt i)

/-- The inclusion of opens attached to a simplicial operator and a source index. -/
@[stacks 02N9 "simplicial-space open inclusion"]
def simplicialSpace.inclusion {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (i : I.obj Δ) :
    U.openAt i ⟶ U.openAt (I.map f i) :=
  homOfLE (U.map_le f i)

/-- The function on degreewise disjoint unions induced by a simplicial operator. -/
@[stacks 02N9 "simplicial-space map function"]
def simplicialSpace.map.toFun {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (Σ i : I.obj Δ, U.openAt i) →
      (Σ i : I.obj Δ', U.openAt i) :=
  fun x ↦
    ⟨I.map f x.1,
      (Opens.toTopCat X).map (simplicialSpace.inclusion U f x.1) x.2⟩

/-- The underlying index of `simplicialSpace.map.toFun` is the simplicial action on indices. -/
@[stacks 02N9 "simplicial-space map index formula", simp]
theorem simplicialSpace.map.toFun.val {Δ Δ' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (x : Σ i : I.obj Δ, U.openAt i) :
    (simplicialSpace.map.toFun U f x).1 = I.map f x.1 := sorry

/-- The map on degreewise disjoint unions induced by a simplicial operator is continuous. -/
@[stacks 02N9 "simplicial-space map continuity"]
theorem simplicialSpace.map.toFun.continuous {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    Continuous (simplicialSpace.map.toFun U f) := sorry

/-- The topological map on degreewise disjoint unions induced by a simplicial operator. -/
@[stacks 02N9 "simplicial-space structure map"]
def simplicialSpace.map {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    TopCat.of (Σ i : I.obj Δ, U.openAt i) ⟶
      TopCat.of (Σ i : I.obj Δ', U.openAt i) :=
  TopCat.ofHom
    ⟨simplicialSpace.map.toFun U f, simplicialSpace.map.toFun.continuous U f⟩

/-- The map induced by an identity simplicial operator is the identity. -/
@[stacks 02N9 "simplicial-space map identity"]
theorem simplicialSpace.map.id (Δ : SimplexCategoryᵒᵖ) :
    simplicialSpace.map U (𝟙 Δ) =
      𝟙 (TopCat.of (Σ i : I.obj Δ, U.openAt i)) := sorry

/-- Maps induced by composable simplicial operators compose in the expected order. -/
@[stacks 02N9 "simplicial-space map composition"]
theorem simplicialSpace.map.comp {Δ Δ' Δ'' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (g : Δ' ⟶ Δ'') :
    simplicialSpace.map U (f ≫ g) =
      simplicialSpace.map U f ≫ simplicialSpace.map U g := sorry

/-- The simplicial topological space associated to a simplicial family of opens. -/
@[stacks 02N9 "simplicial space of a simplicial family of opens"]
def simplicialSpace : SimplicialObject TopCat.{max u v} where
  obj Δ := TopCat.of (Σ i : I.obj Δ, U.openAt i)
  map f := simplicialSpace.map U f
  map_id Δ := simplicialSpace.map.id U Δ
  map_comp f g := simplicialSpace.map.comp U f g

/-- The object of the associated simplicial space is the disjoint union of its indexed opens. -/
@[stacks 02N9 "simplicial-space object formula", simp]
theorem simplicialSpace.obj (Δ : SimplexCategoryᵒᵖ) :
    (simplicialSpace U).obj Δ =
      TopCat.of (Σ i : I.obj Δ, U.openAt i) := sorry

/-- The function from the degree indexed by `Δ` to the base space. -/
@[stacks 02N9 "simplicial-space base function"]
def simplicialSpace.toBase.toFun (Δ : SimplexCategoryᵒᵖ) :
    (Σ i : I.obj Δ, U.openAt i) → X :=
  fun x ↦ (x.2 : X)

/-- The function from an indexed disjoint union to the base space is continuous. -/
@[stacks 02N9 "simplicial-space base-map continuity"]
theorem simplicialSpace.toBase.toFun.continuous (Δ : SimplexCategoryᵒᵖ) :
    Continuous (simplicialSpace.toBase.toFun U Δ) := sorry

/-- The map from a simplicial degree of the associated space to the base space. -/
@[stacks 02N9 "simplicial-space base map"]
def simplicialSpace.toBase (Δ : SimplexCategoryᵒᵖ) : (simplicialSpace U).obj Δ ⟶ X :=
  TopCat.ofHom
    ⟨simplicialSpace.toBase.toFun U Δ, simplicialSpace.toBase.toFun.continuous U Δ⟩

/-- The base map computes by forgetting the index and retaining the underlying point. -/
@[stacks 02N9 "simplicial-space base-map formula", simp]
theorem simplicialSpace.toBase.toFun.apply (Δ : SimplexCategoryᵒᵖ)
    (x : Σ i : I.obj Δ, U.openAt i) :
    simplicialSpace.toBase.toFun U Δ x = x.2 := sorry

/-- The base maps are natural with respect to simplicial operators. -/
@[stacks 02N9 "simplicial-space base-map naturality"]
theorem simplicialSpace.map.comp_toBase {Δ Δ' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') :
    simplicialSpace.map U f ≫ simplicialSpace.toBase U Δ' =
      simplicialSpace.toBase U Δ := sorry

/-- The function from the degree-`n` disjoint union to the base space. -/
@[stacks 02N9 "degreewise simplicial-space base function"]
abbrev simplicialSpace.degree.toBase.toFun (n : ℕ) :
    simplicialSpace.degree.obj U n → X :=
  simplicialSpace.toBase.toFun U (op <| SimplexCategory.mk n)

/-- The map from the degree-`n` disjoint union to the base space. -/
@[stacks 02N9 "degreewise simplicial-space base map"]
abbrev simplicialSpace.degree.toBase (n : ℕ) :
    simplicialSpace.degree.obj U n ⟶ X :=
  simplicialSpace.toBase U (op <| SimplexCategory.mk n)

/-- The degree-`0` augmentation map of the associated simplicial topological space. -/
@[stacks 02N9 "simplicial-space degree-zero augmentation"]
abbrev simplicialSpace.augmentation.zero :
    (simplicialSpace U).obj (op <| SimplexCategory.mk 0) ⟶ X :=
  simplicialSpace.degree.toBase U 0

/-- The degree-zero augmentation satisfies the compatibility condition for an augmented
simplicial object. -/
@[stacks 02N9 "simplicial-space augmentation compatibility"]
theorem simplicialSpace.augmentation.zero.compatible :
    ∀ (i : SimplexCategory) (g₁ g₂ : SimplexCategory.mk 0 ⟶ i),
      simplicialSpace.map U g₁.op ≫ simplicialSpace.augmentation.zero U =
        simplicialSpace.map U g₂.op ≫ simplicialSpace.augmentation.zero U := sorry

/-- The augmented simplicial topological space attached to a simplicial family of opens. -/
@[stacks 02N9 "augmented simplicial space of a simplicial family of opens"]
def simplicialSpace.augmented : SimplicialObject.Augmented TopCat.{max u v} :=
  (simplicialSpace U).augment X (simplicialSpace.augmentation.zero U)
    (simplicialSpace.augmentation.zero.compatible U)

end OpenFamily
end SSet

namespace SSet.OpenHypercovering.ulift

open CategoryTheory

variable {X : Type u} [TopologicalSpace X]
variable (H : OpenHypercovering.{u, v} X)

/-- The simplicial topological space associated to the universe-lifted hypercovering family. -/
@[stacks 02N9 "simplicial space of a universe-lifted open hypercovering"]
abbrev simplicialSpace :
    SimplicialObject TopCat.{max u v} :=
  SSet.OpenFamily.simplicialSpace
    (X := TopCat.of (ULift.{v} X)) H.ulift.family

/-- The canonical augmentation of the universe-lifted hypercovering family. -/
@[stacks 02N9 "augmentation of a universe-lifted open hypercovering"]
abbrev augmented :
    SimplicialObject.Augmented TopCat.{max u v} :=
  SSet.OpenFamily.simplicialSpace.augmented
    (X := TopCat.of (ULift.{v} X)) H.ulift.family

end SSet.OpenHypercovering.ulift

section UniverseBoundary

variable {X : TopCat.{max u v}} {I : SSet.{v}} (U : SSet.OpenFamily X I)

end UniverseBoundary
