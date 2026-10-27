/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.SpacePoint

/-!
# The Hilbert functor as an fppf sheaf on Sch/S

This module realises `Hilb_{X/B}` as an fppf sheaf on `Over S`, and constructs
the canonical comparison from space-level Hilbert pairs to morphisms of sheaves
out of an algebraic space `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Pullback of Hilbert pairs along the identity acts as the identity. -/
theorem hilbertOverFunctor_map_id (f : X ⟶ B) [FinitePresentation f]
    (U : (Over S)ᵒᵖ) :
    TypeCat.ofHom (fun P : SpacePair f (ofOver U.unop) ↦
      P.pullback (ofOverMap (𝟙 U).unop)) =
        𝟙 (SpacePair f (ofOver U.unop)) := sorry

/-- Pullback of Hilbert pairs respects composition of test-scheme morphisms. -/
theorem hilbertOverFunctor_map_comp (f : X ⟶ B) [FinitePresentation f]
    {U V W : (Over S)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W) :
    TypeCat.ofHom (fun P : SpacePair f (ofOver U.unop) ↦
      P.pullback (ofOverMap (φ ≫ ψ).unop)) =
    TypeCat.ofHom (fun P : SpacePair f (ofOver U.unop) ↦
      P.pullback (ofOverMap φ.unop)) ≫
    TypeCat.ofHom (fun P : SpacePair f (ofOver V.unop) ↦
      P.pullback (ofOverMap ψ.unop)) := sorry

/-- The presheaf on schemes over `S` sending `U` to pairs `(h, Z)` with
`h : ofOver U ⟶ B` and `Z` an ideal-sheaf identified closed subspace of
`X_U` that is of finite presentation, flat, and proper over `ofOver U`. -/
def hilbertOverFunctor (f : X ⟶ B) [FinitePresentation f] :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := SpacePair f (ofOver U.unop)
  map {U V} φ :=
    TypeCat.ofHom fun (P : SpacePair f (ofOver U.unop)) ↦
      P.pullback (ofOverMap φ.unop)
  map_id := hilbertOverFunctor_map_id f
  map_comp := hilbertOverFunctor_map_comp f

/-- Evaluating `hilbertOverFunctor` at a scheme over `S` recovers space-level
Hilbert pairs. -/
theorem hilbertOverFunctor_obj (f : X ⟶ B) [FinitePresentation f] (U : Over S) :
    (hilbertOverFunctor f).obj (op U) = SpacePair f (ofOver U) := sorry

/-- The presheaf `hilbertOverFunctor f` is an fppf sheaf on `Over S`. -/
theorem hilbertIsSheaf (f : X ⟶ B) [FinitePresentation f] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (hilbertOverFunctor f) := sorry

/-- The fppf sheaf `Hilb_{X/B}` on `(Sch/S)_fppf`. -/
def hilbertSheaf (f : X ⟶ B) [FinitePresentation f] :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨hilbertOverFunctor f, hilbertIsSheaf f⟩

/-- Evaluating `hilbertSheaf f` at a scheme `U` over `S` recovers space-level
Hilbert pairs on `ofOver U`. -/
theorem hilbertSheaf_obj (f : X ⟶ B) [FinitePresentation f] (U : Over S) :
    (hilbertSheaf f).obj.obj (op U) = SpacePair f (ofOver U) := sorry

/-- The component of the canonical comparison at a scheme `U` over `S`, sending
a `U`-point of `T` to the pullback pair `(h ∘ a, a^* Z)`. -/
def toHilbertSheafHomApp (f : X ⟶ B) [FinitePresentation f]
    {T : AlgebraicSpace S} (P : SpacePair f T) (U : (Over S)ᵒᵖ)
    (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) : SpacePair f (ofOver U.unop) :=
  P.pullback (yonedaEquiv.symm x.down)

/-- The pullback comparison for Hilbert pairs is natural in test schemes. -/
theorem toHilbertSheafHom_naturality (f : X ⟶ B) [FinitePresentation f]
    {T : AlgebraicSpace S} (P : SpacePair f T) {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (AlgebraicSpace.toSheaf.obj T).obj.map φ ≫ TypeCat.ofHom (toHilbertSheafHomApp f P V) =
      TypeCat.ofHom (toHilbertSheafHomApp f P U) ≫ (hilbertOverFunctor f).map φ := sorry

/-- The canonical morphism of fppf sheaves `T ⟶ Hilb_{X/B}` associated to a
pair `(h, Z)` over an algebraic space `T`. -/
def toHilbertSheafHom (f : X ⟶ B) [FinitePresentation f] (T : AlgebraicSpace S)
    (P : SpacePair f T) : AlgebraicSpace.toSheaf.obj T ⟶ hilbertSheaf f :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toHilbertSheafHomApp f P U)
      naturality {_ _} φ := toHilbertSheafHom_naturality f P φ }

/-- On a scheme `U` over `S`, `toHilbertSheafHom` evaluates by pullback along
the corresponding morphism `ofOver U ⟶ T`. -/
theorem toHilbertSheafHom_app (f : X ⟶ B) [FinitePresentation f]
    {T : AlgebraicSpace S} (P : SpacePair f T) (U : (Over S)ᵒᵖ)
    (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) :
    (toHilbertSheafHom f T P).hom.app U x = toHilbertSheafHomApp f P U x := sorry

/-- Pullback of proper, flat, finitely presented closed subspaces gives a
bijection between Hilbert pairs over an algebraic space and morphisms from its
fppf sheaf of points to the Hilbert sheaf. -/
theorem hilbertSheafHom_bijective (f : X ⟶ B) [FinitePresentation f]
    (T : AlgebraicSpace S) :
    Function.Bijective (toHilbertSheafHom f T) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
