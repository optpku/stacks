/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap97.Lemma_97_11_4_RelativeHom
public import stacks_project.Chap99.Lemma_99_7_5_SpacePoint

/-!
# The functor of quotients as an fppf sheaf on Sch/S

This module realises `Q_{F/X/B}` and `Q^{fp}_{F/X/B}` as fppf sheaves on `Over S`,
and constructs the canonical comparison from space-level quotient pairs to morphisms
of sheaves out of an algebraic space `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The presheaf on schemes over `S` sending `U` to pairs `(h, Q)` with
`h : ofOver U ⟶ B` and `Q` a kernel-identified quasi-coherent quotient of `F_U`
flat over `ofOver U`. -/
def overFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := SpaceQuotient f F (ofOver U.unop)
  map {U V} φ :=
    TypeCat.ofHom fun (Q : SpaceQuotient f F (ofOver U.unop)) ↦
      Q.pullback (ofOverMap φ.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating `overFunctor` at a scheme over `S` recovers space-level quotient pairs. -/
theorem overFunctor_obj (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] (U : Over S) :
    (overFunctor f F).obj (op U) = SpaceQuotient f F (ofOver U) := sorry

/-- The presheaf `overFunctor f F` is an fppf sheaf on `Over S`. -/
theorem isSheaf (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (overFunctor f F) := sorry

/-- The fppf sheaf `Q_{F/X/B}` on `(Sch/S)_fppf`. -/
def sheaf (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨overFunctor f F, isSheaf f F⟩

/-- Evaluating `sheaf f F` at a scheme `U` over `S` recovers space-level quotient pairs
on `ofOver U`. -/
theorem sheaf_obj (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] (U : Over S) :
    (sheaf f F).obj.obj (op U) = SpaceQuotient f F (ofOver U) := sorry

/-- The component of the canonical comparison at a scheme `U` over `S`, sending a
`U`-point of `T` to the pullback pair `(h ∘ a, a^* Q)`. -/
def toSheafHomApp (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : SpaceQuotient f F T) (U : (Over S)ᵒᵖ)
    (x : (uliftFunctorOfPoints T).obj U) : SpaceQuotient f F (ofOver U.unop) :=
  Q.pullback (yonedaEquiv.symm x.down)

/-- The canonical morphism of fppf sheaves `T ⟶ Q_{F/X/B}` associated to a pair
`(h, Q)` over an algebraic space `T`. -/
def toSheafHom (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] (T : AlgebraicSpace S)
    (Q : SpaceQuotient f F T) : uliftSheafOfPoints T ⟶ sheaf f F :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toSheafHomApp f F Q U)
      naturality := sorry }

/-- On a scheme `U` over `S`, `toSheafHom` evaluates by pullback along the corresponding
morphism `ofOver U ⟶ T`. -/
theorem toSheafHom_app (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : SpaceQuotient f F T) (U : (Over S)ᵒᵖ)
    (x : (uliftFunctorOfPoints T).obj U) :
    (toSheafHom f F T Q).hom.app U x = toSheafHomApp f F Q U x := sorry

/-- The finitely presented presheaf on schemes over `S` sending `U` to pairs `(h, Q)`
with `h : ofOver U ⟶ B` and `Q` a kernel-identified finitely presented quasi-coherent
quotient of `F_U` flat over `ofOver U`. -/
def fpOverFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := FpSpaceQuotient f F (ofOver U.unop)
  map {U V} φ :=
    TypeCat.ofHom fun (Q : FpSpaceQuotient f F (ofOver U.unop)) ↦
      Q.pullback (ofOverMap φ.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating `fpOverFunctor` at a scheme over `S` recovers finitely presented
space-level quotient pairs. -/
theorem fpOverFunctor_obj (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (U : Over S) :
    (fpOverFunctor f F).obj (op U) = FpSpaceQuotient f F (ofOver U) := sorry

/-- The presheaf `fpOverFunctor f F` is an fppf sheaf on `Over S`. -/
theorem fpIsSheaf (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (fpOverFunctor f F) := sorry

/-- The fppf sheaf `Q^{fp}_{F/X/B}` on `(Sch/S)_fppf`. -/
def fpSheaf (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨fpOverFunctor f F, fpIsSheaf f F⟩

/-- Evaluating `fpSheaf f F` at a scheme `U` over `S` recovers finitely presented
space-level quotient pairs on `ofOver U`. -/
theorem fpSheaf_obj (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] (U : Over S) :
    (fpSheaf f F).obj.obj (op U) = FpSpaceQuotient f F (ofOver U) := sorry

/-- The component of the finitely presented comparison at a scheme `U` over `S`. -/
def toFpSheafHomApp (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : FpSpaceQuotient f F T) (U : (Over S)ᵒᵖ)
    (x : (uliftFunctorOfPoints T).obj U) : FpSpaceQuotient f F (ofOver U.unop) :=
  Q.pullback (yonedaEquiv.symm x.down)

/-- The canonical morphism of fppf sheaves `T ⟶ Q^{fp}_{F/X/B}` associated to a
finitely presented pair `(h, Q)` over an algebraic space `T`. -/
def toFpSheafHom (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (T : AlgebraicSpace S) (Q : FpSpaceQuotient f F T) :
    uliftSheafOfPoints T ⟶ fpSheaf f F :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toFpSheafHomApp f F Q U)
      naturality := sorry }

/-- On a scheme `U` over `S`, `toFpSheafHom` evaluates by pullback along the
corresponding morphism `ofOver U ⟶ T`. -/
theorem toFpSheafHom_app (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : FpSpaceQuotient f F T) (U : (Over S)ᵒᵖ)
    (x : (uliftFunctorOfPoints T).obj U) :
    (toFpSheafHom f F T Q).hom.app U x = toFpSheafHomApp f F Q U x := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
