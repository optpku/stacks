/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport.SpacePoint

/-!
# The Quot functor as an fppf sheaf on Sch/S

This module realises `Quot_{F/X/B}` as an fppf sheaf on `Over S`, and
constructs the canonical comparison from space-level Quot pairs to morphisms
of sheaves out of an algebraic space `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Pullback of proper-support quotient pairs along an identity acts as the identity. -/
theorem quotOverFunctor_map_id (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] (U : (Over S)ᵒᵖ) :
    TypeCat.ofHom (fun Q : QuotSpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap (𝟙 U).unop)) =
        𝟙 (QuotSpaceQuotient f F (ofOver U.unop)) := sorry

/-- Pullback of proper-support quotient pairs respects composition of test-scheme morphisms. -/
theorem quotOverFunctor_map_comp (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent]
    {U V W : (Over S)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W) :
    TypeCat.ofHom (fun Q : QuotSpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap (φ ≫ ψ).unop)) =
    TypeCat.ofHom (fun Q : QuotSpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap φ.unop)) ≫
    TypeCat.ofHom (fun Q : QuotSpaceQuotient f F (ofOver V.unop) ↦
      Q.pullback (ofOverMap ψ.unop)) := sorry

/-- The presheaf on schemes over `S` sending `U` to pairs `(h, Q)` with
`h : ofOver U ⟶ B` and `Q` a kernel-identified finitely presented
quasi-coherent quotient of `F_U` that is flat over `ofOver U` and has support
proper over `ofOver U`. -/
def quotOverFunctor (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := QuotSpaceQuotient f F (ofOver U.unop)
  map {U V} φ :=
    TypeCat.ofHom fun (Q : QuotSpaceQuotient f F (ofOver U.unop)) ↦
      Q.pullback (ofOverMap φ.unop)
  map_id := quotOverFunctor_map_id f F
  map_comp := quotOverFunctor_map_comp f F

/-- Evaluating `quotOverFunctor` at a scheme over `S` recovers space-level Quot
pairs. -/
theorem quotOverFunctor_obj (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (U : Over S) :
    (quotOverFunctor f F).obj (op U) = QuotSpaceQuotient f F (ofOver U) := sorry

/-- The presheaf `quotOverFunctor f F` is an fppf sheaf on `Over S`. -/
theorem quotIsSheaf (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (quotOverFunctor f F) := sorry

/-- The fppf sheaf `Quot_{F/X/B}` on `(Sch/S)_fppf`. -/
def quotSheaf (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨quotOverFunctor f F, quotIsSheaf f F⟩

/-- Evaluating `quotSheaf f F` at a scheme `U` over `S` recovers space-level
Quot pairs on `ofOver U`. -/
theorem quotSheaf_obj (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (U : Over S) :
    (quotSheaf f F).obj.obj (op U) = QuotSpaceQuotient f F (ofOver U) := sorry

/-- The component of the canonical comparison at a scheme `U` over `S`, sending
a `U`-point of `T` to the pullback pair `(h ∘ a, a^* Q)`. -/
def toQuotSheafHomApp (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] {T : AlgebraicSpace S} (Q : QuotSpaceQuotient f F T)
    (U : (Over S)ᵒᵖ) (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) :
    QuotSpaceQuotient f F (ofOver U.unop) :=
  Q.pullback (yonedaEquiv.symm x.down)

/-- The pullback comparison for proper-support quotient pairs is natural in test schemes. -/
theorem toQuotSheafHom_naturality (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] {T : AlgebraicSpace S}
    (Q : QuotSpaceQuotient f F T) {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (AlgebraicSpace.toSheaf.obj T).obj.map φ ≫ TypeCat.ofHom (toQuotSheafHomApp f F Q V) =
      TypeCat.ofHom (toQuotSheafHomApp f F Q U) ≫ (quotOverFunctor f F).map φ := sorry

/-- The canonical morphism of fppf sheaves `T ⟶ Quot_{F/X/B}` associated to a
pair `(h, Q)` over an algebraic space `T`. -/
def toQuotSheafHom (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (T : AlgebraicSpace S) (Q : QuotSpaceQuotient f F T) :
    AlgebraicSpace.toSheaf.obj T ⟶ quotSheaf f F :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toQuotSheafHomApp f F Q U)
      naturality {_ _} φ := toQuotSheafHom_naturality f F Q φ }

/-- On a scheme `U` over `S`, `toQuotSheafHom` evaluates by pullback along the
corresponding morphism `ofOver U ⟶ T`. -/
theorem toQuotSheafHom_app (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] {T : AlgebraicSpace S} (Q : QuotSpaceQuotient f F T)
    (U : (Over S)ᵒᵖ) (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) :
    (toQuotSheafHom f F T Q).hom.app U x = toQuotSheafHomApp f F Q U x := sorry

/-- The component of the inclusion `Quot_{F/X/B} ⟶ Q^{fp}_{F/X/B}` at a scheme
`U` over `S`, sending a proper-support pair to its underlying finitely
presented pair. -/
def quotSheafToFpSheafApp (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (U : (Over S)ᵒᵖ)
    (Q : QuotSpaceQuotient f F (ofOver U.unop)) :
    FpSpaceQuotient f F (ofOver U.unop) :=
  Q.toFpSpaceQuotient

/-- Forgetting proper support commutes with pullback of quotient pairs. -/
theorem quotSheafToFpSheaf_naturality (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (quotOverFunctor f F).map φ ≫ TypeCat.ofHom (quotSheafToFpSheafApp f F V) =
      TypeCat.ofHom (quotSheafToFpSheafApp f F U) ≫ (fpOverFunctor f F).map φ := sorry

/-- The inclusion of fppf sheaves `Quot_{F/X/B} ⟶ Q^{fp}_{F/X/B}` on
`(Sch/S)_fppf`, sending a proper-support pair `(h, Q)` to the same pair as a
finitely presented section. -/
def quotSheafToFpSheaf (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] : quotSheaf f F ⟶ fpSheaf f F :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (quotSheafToFpSheafApp f F U)
      naturality {_ _} φ := quotSheafToFpSheaf_naturality f F φ }

/-- On a scheme `U` over `S`, `quotSheafToFpSheaf` evaluates by forgetting
proper support. -/
theorem quotSheafToFpSheaf_app (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] (U : (Over S)ᵒᵖ)
    (Q : QuotSpaceQuotient f F (ofOver U.unop)) :
    (quotSheafToFpSheaf f F).hom.app U Q = quotSheafToFpSheafApp f F U Q := sorry

/-- The comparison `T ⟶ Quot_{F/X/B}` composed with the inclusion into
`Q^{fp}_{F/X/B}` recovers the finitely presented comparison of the underlying
pair. -/
theorem toQuotSheafHom_comp_quotSheafToFpSheaf (f : X ⟶ B)
    [FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : QuotSpaceQuotient f F T) :
    toQuotSheafHom f F T Q ≫ quotSheafToFpSheaf f F =
      toFpSheafHom f F T Q.toFpSpaceQuotient := sorry

/-- Pullback of finitely presented flat quotient pairs with proper support gives a
bijection with morphisms from the fppf sheaf of points of an algebraic space to the
proper-support quotient sheaf. -/
theorem quotSheafHom_bijective (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] (T : AlgebraicSpace S) :
    Function.Bijective (toQuotSheafHom f F T) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
