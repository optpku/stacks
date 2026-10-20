/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap97.Lemma_97_11_4_RelativeHom
public import stacks_project.Chap99.Lemma_99_9_3_SpacePoint

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

/-- The presheaf on schemes over `S` sending `U` to pairs `(h, Z)` with
`h : ofOver U ⟶ B` and `Z` an ideal-sheaf identified closed subspace of
`X_U` that is of finite presentation, flat, and proper over `ofOver U`. -/
def hilbertOverFunctor (f : X ⟶ B) [FinitePresentation f] :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := SpacePair f (ofOver U.unop)
  map {U V} φ :=
    TypeCat.ofHom fun (P : SpacePair f (ofOver U.unop)) ↦
      P.pullback (ofOverMap φ.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating `hilbertOverFunctor` at a scheme over `S` recovers space-level
Hilbert pairs. -/
theorem hilbertOverFunctor_obj (f : X ⟶ B) [FinitePresentation f] (U : Over S) :
    (hilbertOverFunctor f).obj (op U) = SpacePair f (ofOver U) :=
  sorry

/-- The presheaf `hilbertOverFunctor f` is an fppf sheaf on `Over S`. -/
theorem hilbertIsSheaf (f : X ⟶ B) [FinitePresentation f] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (hilbertOverFunctor f) :=
  sorry

/-- The fppf sheaf `Hilb_{X/B}` on `(Sch/S)_fppf`. -/
def hilbertSheaf (f : X ⟶ B) [FinitePresentation f] :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨hilbertOverFunctor f, hilbertIsSheaf f⟩

/-- Evaluating `hilbertSheaf f` at a scheme `U` over `S` recovers space-level
Hilbert pairs on `ofOver U`. -/
theorem hilbertSheaf_obj (f : X ⟶ B) [FinitePresentation f] (U : Over S) :
    (hilbertSheaf f).obj.obj (op U) = SpacePair f (ofOver U) :=
  sorry

/-- The component of the canonical comparison at a scheme `U` over `S`, sending
a `U`-point of `T` to the pullback pair `(h ∘ a, a^* Z)`. -/
def toHilbertSheafHomApp (f : X ⟶ B) [FinitePresentation f]
    {T : AlgebraicSpace S} (P : SpacePair f T) (U : (Over S)ᵒᵖ)
    (x : (uliftFunctorOfPoints T).obj U) : SpacePair f (ofOver U.unop) :=
  P.pullback (yonedaEquiv.symm x.down)

/-- The canonical morphism of fppf sheaves `T ⟶ Hilb_{X/B}` associated to a
pair `(h, Z)` over an algebraic space `T`. -/
def toHilbertSheafHom (f : X ⟶ B) [FinitePresentation f] (T : AlgebraicSpace S)
    (P : SpacePair f T) : uliftSheafOfPoints T ⟶ hilbertSheaf f :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toHilbertSheafHomApp f P U)
      naturality := sorry }

/-- On a scheme `U` over `S`, `toHilbertSheafHom` evaluates by pullback along
the corresponding morphism `ofOver U ⟶ T`. -/
theorem toHilbertSheafHom_app (f : X ⟶ B) [FinitePresentation f]
    {T : AlgebraicSpace S} (P : SpacePair f T) (U : (Over S)ᵒᵖ)
    (x : (uliftFunctorOfPoints T).obj U) :
    (toHilbertSheafHom f T P).hom.app U x = toHilbertSheafHomApp f P U x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
