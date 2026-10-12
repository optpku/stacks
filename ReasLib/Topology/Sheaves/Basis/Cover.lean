/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import ReasLib.Topology.Sheaves.Basis.Basic

/-!
# Sheaves on a topological basis

This module defines the site of opens belonging to an arbitrary collection `B`.  The induced
Grothendieck topology exists without assuming that `B` is a basis; the basis hypothesis enters
only in comparison results with sheaves on the ambient space.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v w

variable {X : Type u} [TopologicalSpace X]

/-- The inclusion of basis opens is cover-dense when `B` is a topological basis. -/
theorem basisOpenInclusion_isCoverDense {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) := sorry

/-- The Grothendieck topology on basis opens induced by the topology on all opens. -/
noncomputable abbrev basisGrothendieckTopology (B : Set (Opens X)) :
    GrothendieckTopology (BasisOpen B) :=
  (basisOpenInclusion B).inducedTopology (Opens.grothendieckTopology X)

/-- The canonical category of `C`-valued sheaves on the induced basis-open site. -/
abbrev BasisSiteSheaf (C : Type v) [Category.{w} C] (B : Set (Opens X)) :=
  Sheaf (basisGrothendieckTopology B) C

/-- A covering of an open `U` by members of `B`. -/
structure BasisCover (B : Set (Opens X)) (U : BasisOpen B) where
  /-- The index type of the covering family. -/
  ι : Type u
  /-- The member of `B` indexed by `i`. -/
  obj : ι → BasisOpen B
  /-- The inclusion of the `i`-th member into `U`. -/
  hom : ∀ i : ι, obj i ⟶ U
  /-- The union of the members of the family is `U`. -/
  iUnion_eq : (U.obj : Set X) = ⋃ i : ι, ((obj i).obj : Set X)

/-- Chosen coverings by members of `B` of the pairwise intersections in a `BasisCover`. -/
structure BasisIntersectionCover (B : Set (Opens X)) {U : BasisOpen B}
    (𝒰 : BasisCover B U) where
  /-- The index type for the chosen cover of `Uᵢ ∩ Uⱼ`. -/
  κ : 𝒰.ι → 𝒰.ι → Type u
  /-- The members of `B` covering each pairwise intersection. -/
  obj (i j : 𝒰.ι) (k : κ i j) : BasisOpen B
  /-- The inclusion of a chosen overlap open into the left member of the pair. -/
  left (i j : 𝒰.ι) (k : κ i j) : obj i j k ⟶ 𝒰.obj i
  /-- The inclusion of a chosen overlap open into the right member of the pair. -/
  right (i j : 𝒰.ι) (k : κ i j) : obj i j k ⟶ 𝒰.obj j
  /-- The chosen overlap family covers `Uᵢ ∩ Uⱼ`. -/
  iUnion_eq (i j : 𝒰.ι) :
    (((𝒰.obj i).obj ⊓ (𝒰.obj j).obj : Opens X) : Set X) =
      ⋃ k, ((obj i j k).obj : Set X)

namespace BasisCover

variable {B : Set (Opens X)} {U : BasisOpen B}

/-- The unique-amalgamation condition for a basis cover, tested on a chosen cover of every
pairwise intersection. -/
def HasSheafCondition (F : (BasisOpen B)ᵒᵖ ⥤ Type v) (𝒰 : BasisCover B U)
    (𝒱 : BasisIntersectionCover B 𝒰) : Prop :=
  ∀ s : Presheaf.FamilyOfElementsOnObjects F 𝒰.obj,
    (∀ i j k, F.map ((𝒱.left i j k).op) (s i) = F.map ((𝒱.right i j k).op) (s j)) →
      ∃! t : F.obj (op U), ∀ i, F.map ((𝒰.hom i).op) t = s i

/-- Every compatible family on a basis cover has a unique amalgamation. -/
@[stacks 0F1A "unique gluing for a basis cover"]
def HasUniqueGluing (𝒰 : BasisCover B U)
    (F : (BasisOpen B)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ s : Presheaf.FamilyOfElementsOnObjects F 𝒰.obj,
    s.IsCompatible →
      ∃! t : F.obj (op U), ∀ i, F.map ((𝒰.hom i).op) t = s i

/-- The actual intersection of two members of a basis cover, when that intersection belongs to
the basis. -/
abbrev actualIntersection
    (𝒰 : BasisCover B U)
    (h_inter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) : BasisOpen B :=
  ⟨(𝒰.obj i).obj ⊓ (𝒰.obj j).obj, h_inter i j⟩

/-- The actual intersection maps into the left member of the basis cover. -/
abbrev actualIntersectionLeft
    (𝒰 : BasisCover B U)
    (h_inter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) :
    actualIntersection 𝒰 h_inter i j ⟶ 𝒰.obj i :=
  ⟨homOfLE inf_le_left⟩

/-- The actual intersection maps into the right member of the basis cover. -/
abbrev actualIntersectionRight
    (𝒰 : BasisCover B U)
    (h_inter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) :
    actualIntersection 𝒰 h_inter i j ⟶ 𝒰.obj j :=
  ⟨homOfLE inf_le_right⟩

/-- Compatibility of a family on a basis cover is equivalent to compatibility on the actual
pairwise intersections, when those intersections belong to the basis. -/
theorem isCompatible_iff_actualIntersections
    (𝒰 : BasisCover B U)
    (h_inter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : (BasisOpen B)ᵒᵖ ⥤ Type v)
    (s : Presheaf.FamilyOfElementsOnObjects F 𝒰.obj) :
    s.IsCompatible ↔
      ∀ i j : 𝒰.ι,
        F.map ((actualIntersectionLeft 𝒰 h_inter i j).op) (s i) =
          F.map ((actualIntersectionRight 𝒰 h_inter i j).op) (s j) := sorry

/-- The singleton family consisting of the actual pairwise intersection covers that
intersection. -/
theorem singletonActualIntersectionCover_iUnion_eq
    (𝒰 : BasisCover B U)
    (h_inter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) :
    ((((𝒰.obj i).obj ⊓ (𝒰.obj j).obj : Opens X) : Set X)) =
      ⋃ _ : PUnit, ((actualIntersection 𝒰 h_inter i j).obj : Set X) := sorry

/-- A basis-intersection cover obtained by using each actual pairwise intersection as a singleton
cover. -/
def singletonActualIntersectionCover
    (𝒰 : BasisCover B U)
    (h_inter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B) :
    BasisIntersectionCover B 𝒰 where
  κ _ _ := PUnit
  obj i j _ := actualIntersection 𝒰 h_inter i j
  left i j _ := actualIntersectionLeft 𝒰 h_inter i j
  right i j _ := actualIntersectionRight 𝒰 h_inter i j
  iUnion_eq i j := singletonActualIntersectionCover_iUnion_eq 𝒰 h_inter i j

/-- For singleton actual-intersection covers, the basis-cover sheaf condition is equivalent to
existence and uniqueness of an amalgamation for every compatible family. -/
theorem hasSheafCondition_iff_uniqueGluing_actualIntersections
    (𝒰 : BasisCover B U)
    (h_inter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : (BasisOpen B)ᵒᵖ ⥤ Type v) :
    𝒰.HasSheafCondition F (singletonActualIntersectionCover 𝒰 h_inter) ↔
      𝒰.HasUniqueGluing F := sorry

end BasisCover

namespace CategoryTheory.Presheaf

variable {B : Set (Opens X)}

/-- A set-valued presheaf on a collection of opens satisfies the basis-cover sheaf condition. -/
def IsBasisSheaf (F : (BasisOpen B)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U) (𝒱 : BasisIntersectionCover B 𝒰),
    𝒰.HasSheafCondition F 𝒱

end CategoryTheory.Presheaf

/-- The full subcategory of set-valued presheaves satisfying the basis-cover sheaf condition. -/
abbrev BasisSheaf (B : Set (Opens X)) :=
  ObjectProperty.FullSubcategory fun F : (BasisOpen B)ᵒᵖ ⥤ Type v ↦
    Presheaf.IsBasisSheaf F
