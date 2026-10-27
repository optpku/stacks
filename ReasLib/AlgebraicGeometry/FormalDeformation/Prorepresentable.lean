/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Inclusion
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Functor

@[expose] public section

open CategoryTheory Opposite

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Restriction of the covariant coyoneda functor represented by a complete local algebra. -/
noncomputable def restrictedCoyoneda (R : CompleteLocalAlgCat Λ k) :
    ArtinianLocalAlgCat Λ k ⥤ Type u :=
  ArtinianLocalAlgCat.inclusion ⋙ coyoneda.obj (op R)

/-- The restricted coyoneda functor evaluates at an Artinian object as a morphism from `R`. -/
theorem restrictedCoyoneda_obj (R : CompleteLocalAlgCat Λ k) (A : ArtinianLocalAlgCat Λ k) :
    (restrictedCoyoneda R).obj A = (R ⟶ ArtinianLocalAlgCat.inclusion.obj A) := rfl

/-- The restricted coyoneda functor maps by postcomposition with the included morphism. -/
theorem restrictedCoyoneda_map (R : CompleteLocalAlgCat Λ k)
    {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    (restrictedCoyoneda R).map f =
      (coyoneda.obj (op R)).map (ArtinianLocalAlgCat.inclusion.map f) := rfl

/-- The morphism of restricted coyoneda functors induced by `f : R ⟶ S`, obtained by
whiskering `coyoneda.map f.op` with `ArtinianLocalAlgCat.inclusion`. -/
noncomputable def restrictedCoyonedaMap {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    restrictedCoyoneda S ⟶ restrictedCoyoneda R :=
  ArtinianLocalAlgCat.inclusion.whiskerLeft (coyoneda.map f.op)

/-- The component of `restrictedCoyonedaMap f` at `A` is precomposition with `f`. -/
theorem restrictedCoyonedaMap_app {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (A : ArtinianLocalAlgCat Λ k) (g : S ⟶ ArtinianLocalAlgCat.inclusion.obj A) :
    (restrictedCoyonedaMap f).app A g = f ≫ g :=
  rfl

/-- The restricted coyoneda map of an identity is the identity transformation. -/
theorem restrictedCoyonedaMap_id (R : CompleteLocalAlgCat Λ k) :
    restrictedCoyonedaMap (𝟙 R) = 𝟙 (restrictedCoyoneda R) := by
  ext A g
  exact Category.id_comp g

/-- Restricted coyoneda maps reverse composition of morphisms in `CompleteLocalAlgCat`. -/
theorem restrictedCoyonedaMap_comp {R S T : CompleteLocalAlgCat Λ k}
    (f : R ⟶ S) (g : S ⟶ T) :
    restrictedCoyonedaMap (f ≫ g) = restrictedCoyonedaMap g ≫ restrictedCoyonedaMap f := by
  ext A h
  exact Category.assoc f g h

end CompleteLocalAlgCat

namespace CategoryTheory.Functor

/-- A functor on Artinian local algebras is prorepresentable when represented by a complete local algebra. -/
class IsProrepresentable (F : ArtinianLocalAlgCat Λ k ⥤ Type u) : Prop where
  has_prorepresentation :
    ∃ R : CompleteLocalAlgCat Λ k, Nonempty (CompleteLocalAlgCat.restrictedCoyoneda R ≅ F)

/-- Each restricted coyoneda functor is prorepresentable by its representing complete local algebra. -/
instance instIsProrepresentableRestrictedCoyoneda (R : CompleteLocalAlgCat Λ k) :
    IsProrepresentable (CompleteLocalAlgCat.restrictedCoyoneda R) :=
  ⟨⟨R, ⟨Iso.refl _⟩⟩⟩

/-- Prorepresentability is equivalent to the existence of a representing complete local algebra. -/
theorem isProrepresentable_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    IsProrepresentable F ↔
      ∃ R : CompleteLocalAlgCat Λ k, Nonempty (CompleteLocalAlgCat.restrictedCoyoneda R ≅ F) :=
  ⟨fun h ↦ h.has_prorepresentation, fun h ↦ ⟨h⟩⟩

/-- Prorepresentability is preserved by isomorphisms of functors. -/
theorem isProrepresentable_of_iso
    {F G : ArtinianLocalAlgCat Λ k ⥤ Type u} (e : F ≅ G)
    [IsProrepresentable F] : IsProrepresentable G := by
  obtain ⟨R, ⟨h⟩⟩ := IsProrepresentable.has_prorepresentation (F := F)
  exact ⟨⟨R, ⟨h ≪≫ e⟩⟩⟩

/-- A prorepresentable functor has a singleton value at the residue field. -/
instance instIsPredeformationFunctor_of_isProrepresentable
    {F : ArtinianLocalAlgCat Λ k ⥤ Type u} [IsProrepresentable F] :
    IsPredeformationFunctor F := by
  obtain ⟨R, ⟨e⟩⟩ := IsProrepresentable.has_prorepresentation (F := F)
  letI : Unique ((CompleteLocalAlgCat.restrictedCoyoneda R).obj
      (ArtinianLocalAlgCat.residue Λ k)) := CompleteLocalAlgCat.instUnique_hom_residue R
  exact ⟨⟨Function.Surjective.unique _
    (e.app (ArtinianLocalAlgCat.residue Λ k)).toEquiv.surjective⟩⟩

/-- The category-of-elements projection of a prorepresentable functor is a deformation category. -/
instance instIsDeformationCategory_π
    {F : ArtinianLocalAlgCat Λ k ⥤ Type u} [IsProrepresentable F] :
    IsDeformationCategory (CategoryOfElements.π F) := sorry

end CategoryTheory.Functor
