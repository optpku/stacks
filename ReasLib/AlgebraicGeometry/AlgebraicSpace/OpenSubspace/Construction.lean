/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.CategoryTheory.MorphismProperty.Representable.MonoDiagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-! # The actual open subspace determined by an open set of points

The carrier contains precisely those scheme-valued sections whose image lies in the
specified open. Its atlas is the corresponding open restriction of the original input atlas.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (W : Opens (Points X))

/-- The actual subfunctor of sections whose scheme points lie in the open set. -/
def subfunctor : Subfunctor X.functorOfPoints where
  obj T := { s | Set.range (Points.map (X := ofOver T.unop) (Y := X)
    (yonedaEquiv.symm s : ofOver T.unop ⟶ X)) ⊆ W }
  map := sorry

/-- A section belongs to the open subfunctor exactly when all its scheme points
map into the specified open set. -/
theorem mem_subfunctor_iff_mapOfOver (T : (Over S)ᵒᵖ)
    (s : X.functorOfPoints.obj T) :
    s ∈ (subfunctor X W).obj T ↔
      Set.range (Points.mapOfOver (yonedaEquiv.symm s : ofOver T.unop ⟶ X)) ⊆
        (W : Set (Points X)) := by
  change Set.range (Points.map (X := ofOver T.unop) (Y := X)
    (yonedaEquiv.symm s : ofOver T.unop ⟶ X)) ⊆ (W : Set (Points X)) ↔ _
  unfold Points.mapOfOver
  constructor
  · rintro h _ ⟨p, rfl⟩
    exact h ⟨_, rfl⟩
  · rintro h _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := (ofOver.pointsEquiv T.unop).surjective p
    exact h ⟨q, rfl⟩

/-- The chosen input atlas restricted to the inverse image of the specified open. -/
def atlasOpens : (AtlasInput.scheme X).left.Opens :=
  ⟨Points.mapOfOver (AtlasInput.map X) ⁻¹' W, sorry⟩

/-- The actual open scheme over the original base. -/
def atlas : Over S :=
  Over.mk ((atlasOpens X W).ι ≫ (AtlasInput.scheme X).hom)

/-- The actual scheme map from the restricted atlas to the input atlas. -/
def atlasInclusion : atlas X W ⟶ AtlasInput.scheme X :=
  Over.homMk (atlasOpens X W).ι rfl

/-- The atlas map into the ambient functor retains the original input atlas map. -/
def ambientAtlasMap : yoneda.obj (atlas X W) ⟶ X.functorOfPoints :=
  yoneda.map (atlasInclusion X W) ≫ AtlasInput.map X

/-- Every point of the restricted atlas lies in the prescribed open. -/
theorem ambientAtlasMap_mem (T : (Over S)ᵒᵖ) (s : (yoneda.obj (atlas X W)).obj T) :
    (ambientAtlasMap X W).app T s ∈ (subfunctor X W).obj T := sorry

/-- The actual restricted atlas maps to the subtype functor by the same section map. -/
def atlasMap : yoneda.obj (atlas X W) ⟶ (subfunctor X W).toFunctor where
  app T := TypeCat.ofHom fun s ↦ ⟨(ambientAtlasMap X W).app T s,
    ambientAtlasMap_mem X W T s⟩
  naturality := sorry

/-- The actual open functor satisfies fppf descent. -/
theorem isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S)
    (subfunctor X W).toFunctor := sorry

/-- The diagonal of the specified open functor inherits the ambient represented pullbacks. -/
theorem representableDiagonal : yoneda.relativelyRepresentable
    (CategoryTheory.Limits.diag (subfunctor X W).toFunctor) :=
  Functor.relativelyRepresentable.diagonal_of_mono
    (D := (Over S)ᵒᵖ ⥤ Type u) yoneda (subfunctor X W).ι
    X.representableDiagonal

/-- The specified restricted atlas is representable and étale. -/
theorem atlas_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
    (atlasMap X W) := sorry

/-- The specified restricted atlas is locally surjective. -/
theorem atlas_surjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
    (atlasMap X W) := sorry

/-- The actual algebraic space carried by the open subfunctor and its restricted atlas. -/
def space : AlgebraicSpace S :=
  AlgebraicSpace.ofFunctor (subfunctor X W).toFunctor
    (isSheaf X W) (representableDiagonal X W)
    ⟨atlas X W, atlasMap X W, atlas_etale X W, atlas_surjective X W⟩

/-- The open subspace inclusion is the subtype projection on every scheme test. -/
def ι : space X W ⟶ X := (subfunctor X W).ι

/-- The actual subtype inclusion is an open immersion. -/
instance inclusion_isOpenImmersion : IsOpenImmersion (ι X W) := sorry

/-- The constructed open subspace has exactly the prescribed open point set. -/
theorem inclusion_range : Set.range (Points.map (ι X W)) = W := sorry

variable {X W}

/-- A section of a morphism whose image lies in the open belongs to its subtype functor. -/
theorem lift_mem {Y : AlgebraicSpace S} (f : Y ⟶ X)
    (h : Set.range (Points.map f) ⊆ W) (T : (Over S)ᵒᵖ)
    (s : Y.functorOfPoints.obj T) : f.app T s ∈ (subfunctor X W).obj T := sorry

/-- Lift a morphism through the actual open by retaining each section and its image law. -/
def lift {Y : AlgebraicSpace S} (f : Y ⟶ X) (h : Set.range (Points.map f) ⊆ W) :
    Y ⟶ space X W where
  app T := TypeCat.ofHom fun s ↦ ⟨f.app T s, lift_mem f h T s⟩
  naturality := sorry

/-- Composing the concrete lift with the subtype inclusion recovers the original map. -/
@[reassoc]
theorem lift_ι {Y : AlgebraicSpace S} (f : Y ⟶ X)
    (h : Set.range (Points.map f) ⊆ W) : lift f h ≫ ι X W = f := rfl

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace
variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The open subspace constructed from the given open set of points. -/
def fromOpens (W : Opens (Points X)) : OpenSubspace X where
  X := Construction.space X W
  ι := Construction.ι X W
  isOpenImmersion := Construction.inclusion_isOpenImmersion X W

/-- The point set of the constructed open is the given open. -/
@[simp]
theorem fromOpens_pointsSet (W : Opens (Points X)) :
    (fromOpens W).pointsSet = W := Construction.inclusion_range X W

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
