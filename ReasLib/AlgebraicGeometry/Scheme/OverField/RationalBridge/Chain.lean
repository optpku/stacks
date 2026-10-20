/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Combinatorics.Quiver.Path
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Genus
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.Contraction
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RationalBridge

/-- A single rational-bridge contraction with its auxiliary maps and target no-tail property. -/
structure ContractionStep {k : Type u} [Field k]
    (X Y : SchemeOverField k) where
  /-- The rational bridge selected for contraction. -/
  bridge : RationalBridge X
  /-- The contraction morphism over the base field. -/
  hom : X ⟶ Y
  /-- The map from the complementary closure to the target. -/
  complementMap : (complementScheme X bridge.component).left ⟶ Y.left
  /-- The map from the component section spectrum to the target. -/
  sectionMap : Spec (Scheme.globalSectionsRing
      (componentScheme X bridge.component).left) ⟶ Y.left
  /-- The map from the component to the target. -/
  componentMap : (componentScheme X bridge.component).left ⟶ Y.left
  /-- The map from the component to its section spectrum. -/
  componentToSpec : (componentScheme X bridge.component).left ⟶
    Spec (Scheme.globalSectionsRing (componentScheme X bridge.component).left)
  /-- The map from the intersection to the component section spectrum. -/
  intersectionToSpec : (intersectionScheme X bridge.component).left ⟶
    Spec (Scheme.globalSectionsRing (componentScheme X bridge.component).left)
  /-- The one-step contraction satisfies the rational-bridge contraction specification. -/
  isContraction : bridge.IsContraction Y hom complementMap sectionMap componentMap
    componentToSpec intersectionToSpec
  /-- The contraction target has no rational tails. -/
  target_no_tail : ¬ Nonempty (SchemeOverField.RationalTail Y)

/-- Construct a rational-bridge contraction step from its maps and contraction law. -/
def ContractionStep.ofData {k : Type u} [Field k]
    (X Y : SchemeOverField k) (bridge : RationalBridge X) (hom : X ⟶ Y)
    (complementMap : (complementScheme X bridge.component).left ⟶ Y.left)
    (sectionMap : Spec (Scheme.globalSectionsRing
      (componentScheme X bridge.component).left) ⟶ Y.left)
    (componentMap : (componentScheme X bridge.component).left ⟶ Y.left)
    (componentToSpec : (componentScheme X bridge.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X bridge.component).left))
    (intersectionToSpec : (intersectionScheme X bridge.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X bridge.component).left))
    (isContraction : bridge.IsContraction Y hom complementMap sectionMap componentMap
      componentToSpec intersectionToSpec)
    (target_no_tail : ¬ Nonempty (SchemeOverField.RationalTail Y)) :
    ContractionStep X Y :=
  { bridge := bridge
    hom := hom
    complementMap := complementMap
    sectionMap := sectionMap
    componentMap := componentMap
    componentToSpec := componentToSpec
    intersectionToSpec := intersectionToSpec
    isContraction := isContraction
    target_no_tail := target_no_tail }

/-- A contraction step satisfies its displayed contraction specification and has no rational
tails at its target. -/
theorem ContractionStep.spec {k : Type u} [Field k] {X Y : SchemeOverField k}
    (step : ContractionStep X Y) :
    step.bridge.IsContraction Y step.hom step.complementMap step.sectionMap step.componentMap
      step.componentToSpec step.intersectionToSpec ∧
    ¬ Nonempty (SchemeOverField.RationalTail Y) := sorry

/-- A finite sequence of rational-bridge contractions from a source to an explicit endpoint,
represented as a path in the reversed quiver of contraction steps. -/
def ContractionChain {k : Type u} [Field k]
    (X Y : SchemeOverField k) :=
  @Quiver.Path (SchemeOverField k) ⟨fun target source => ContractionStep source target⟩ Y X

namespace ContractionChain

/-- The empty contraction sequence from a scheme to itself. -/
def refl {k : Type u} [Field k] (X : SchemeOverField k) : ContractionChain X X :=
  @Quiver.Path.nil (SchemeOverField k) ⟨fun target source => ContractionStep source target⟩ X

/-- Prepend one contraction step to a finite contraction sequence. -/
def cons {k : Type u} [Field k] {X Y Z : SchemeOverField k}
    (step : ContractionStep X Y) (tail : ContractionChain Y Z) : ContractionChain X Z :=
  @Quiver.Path.cons (SchemeOverField k) ⟨fun target source => ContractionStep source target⟩
    Z Y X tail step

/-- The induced morphism is the composite of the maps in a finite contraction sequence. -/
def map {k : Type u} [Field k] {X Y : SchemeOverField k}
    (chain : ContractionChain X Y) : X ⟶ Y :=
  @Quiver.Path.rec (SchemeOverField k) ⟨fun target source => ContractionStep source target⟩
    Y (fun source _ => source ⟶ Y) (𝟙 Y)
    (fun {_ _} _ step tailMap => step.hom ≫ tailMap) X chain

/-- The composite map of an empty contraction sequence is the identity. -/
theorem map_refl {k : Type u} [Field k]
    (X : SchemeOverField k) : (ContractionChain.refl X : ContractionChain X X).map = 𝟙 X := sorry

/-- The composite map of a cons sequence is the first map followed by the tail composite. -/
theorem map_cons {k : Type u} [Field k]
    {X Y Z : SchemeOverField k} (step : ContractionStep X Y)
    (tail : ContractionChain Y Z) :
    (ContractionChain.cons step tail).map = step.hom ≫ tail.map := sorry

/-- A contraction chain preserves properness of its source and endpoint. -/
theorem target_proper {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] (chain : ContractionChain X Y) : IsProper Y.hom := sorry

/-- A contraction chain preserves the one-dimensionality of its source. -/
theorem target_dimension {k : Type u} [Field k]
    {X Y : SchemeOverField k} (chain : ContractionChain X Y)
    (h_dimension : topologicalKrullDim X.left = 1) :
    topologicalKrullDim Y.left = 1 := sorry

/-- A contraction chain preserves constant global functions. -/
theorem target_globalSections {k : Type u} [Field k]
    {X Y : SchemeOverField k} (chain : ContractionChain X Y)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom) := sorry

/-- A contraction chain preserves at-worst-nodal singularities. -/
theorem target_atWorstNodal {k : Type u} [Field k]
    {X Y : SchemeOverField k} (chain : ContractionChain X Y)
    (h_nodal : SchemeOverField.atWorstNodal X) :
    SchemeOverField.atWorstNodal Y := sorry

/-- A contraction chain preserves the absence of rational tails. -/
theorem target_noTail {k : Type u} [Field k]
    {X Y : SchemeOverField k} (chain : ContractionChain X Y)
    (h_no_tail : ¬ Nonempty (SchemeOverField.RationalTail X)) :
    ¬ Nonempty (SchemeOverField.RationalTail Y) := sorry

/-- A contraction chain preserves the genus lower bound, using its endpoint invariants. -/
theorem target_genus {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] (chain : ContractionChain X Y)
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : (2 : ℕ) ≤ SchemeOverField.genus X h_dimension h_global) :
    (2 : ℕ) ≤ @SchemeOverField.genus k _ Y (chain.target_proper)
      (chain.target_dimension h_dimension) (chain.target_globalSections h_global) := sorry

end ContractionChain

end RationalBridge

end AlgebraicGeometry
