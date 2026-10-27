/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.Fpqc
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.SpacePoint

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- The functor of kernel-identified quasi-coherent quotients of `F`, flat over
the test scheme, is a sheaf for the fpqc topology on schemes over `B`. -/
theorem functor_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (functor f F) := sorry

/-- Compatible families of kernel-identified quasi-coherent quotients of `F`,
flat over the test schemes of an fpqc covering, glue uniquely. -/
theorem functor_isSheafFor_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_fpqc : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U) :
    Presieve.IsSheafFor (functor f F) (Presieve.ofArrows V h) := sorry

/-- The functor of finitely presented kernel-identified quasi-coherent quotients
of `F`, flat over the test scheme, is a sheaf for the fpqc topology on schemes
over `B`. -/
theorem fpFunctor_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (fpFunctor f F) := sorry

/-- Compatible families of finitely presented kernel-identified quasi-coherent
quotients of `F`, flat over the test schemes of an fpqc covering, glue uniquely. -/
theorem fpFunctor_isSheafFor_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_fpqc : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U) :
    Presieve.IsSheafFor (fpFunctor f F) (Presieve.ofArrows V h) := sorry

/-- The functor of finitely presented quasi-coherent quotients of `F`, flat
over the test scheme and with proper support, is a sheaf for the fpqc topology
on schemes over `B`. -/
theorem quot_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (quot f F) := sorry

open CategoryTheory.Limits TypeCat

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Pullback of quotient pairs along an identity acts as the identity. -/
theorem overFunctor_map_id (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (U : (Over S)ᵒᵖ) :
    TypeCat.ofHom (fun Q : SpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap (𝟙 U).unop)) =
        𝟙 (SpaceQuotient f F (ofOver U.unop)) := sorry

/-- Pullback of quotient pairs respects composition of test-scheme morphisms. -/
theorem overFunctor_map_comp (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {U V W : (Over S)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W) :
    TypeCat.ofHom (fun Q : SpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap (φ ≫ ψ).unop)) =
    TypeCat.ofHom (fun Q : SpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap φ.unop)) ≫
    TypeCat.ofHom (fun Q : SpaceQuotient f F (ofOver V.unop) ↦
      Q.pullback (ofOverMap ψ.unop)) := sorry

/-- The presheaf on schemes over `S` sending `U` to pairs `(h, Q)` with
`h : ofOver U ⟶ B` and `Q` a kernel-identified quasi-coherent quotient of `F_U`
flat over `ofOver U`. -/
def overFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := SpaceQuotient f F (ofOver U.unop)
  map {U V} (φ : U ⟶ V) :=
    TypeCat.ofHom fun (Q : SpaceQuotient f F (ofOver U.unop)) ↦
      Q.pullback (ofOverMap φ.unop)
  map_id := overFunctor_map_id f F
  map_comp := overFunctor_map_comp f F

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
    (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) : SpaceQuotient f F (ofOver U.unop) :=
  Q.pullback (yonedaEquiv.symm x.down)

/-- The pullback comparison for quotient pairs is natural in test schemes. -/
theorem toSheafHom_naturality (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : SpaceQuotient f F T)
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (AlgebraicSpace.toSheaf.obj T).obj.map φ ≫ TypeCat.ofHom (toSheafHomApp f F Q V) =
      TypeCat.ofHom (toSheafHomApp f F Q U) ≫ (overFunctor f F).map φ := sorry

/-- The canonical morphism of fppf sheaves `T ⟶ Q_{F/X/B}` associated to a pair
`(h, Q)` over an algebraic space `T`. -/
def toSheafHom (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] (T : AlgebraicSpace S)
    (Q : SpaceQuotient f F T) : (AlgebraicSpace.toSheaf.obj T) ⟶ sheaf f F :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toSheafHomApp f F Q U)
      naturality {_ _} φ := toSheafHom_naturality f F Q φ }

/-- On a scheme `U` over `S`, `toSheafHom` evaluates by pullback along the corresponding
morphism `ofOver U ⟶ T`. -/
theorem toSheafHom_app (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : SpaceQuotient f F T) (U : (Over S)ᵒᵖ)
    (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) :
    (toSheafHom f F T Q).hom.app U x = toSheafHomApp f F Q U x := sorry

/-- Pullback of finitely presented quotient pairs along an identity acts as the identity. -/
theorem fpOverFunctor_map_id (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (U : (Over S)ᵒᵖ) :
    TypeCat.ofHom (fun Q : FpSpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap (𝟙 U).unop)) =
        𝟙 (FpSpaceQuotient f F (ofOver U.unop)) := sorry

/-- Pullback of finitely presented quotient pairs respects composition of test-scheme morphisms. -/
theorem fpOverFunctor_map_comp (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {U V W : (Over S)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W) :
    TypeCat.ofHom (fun Q : FpSpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap (φ ≫ ψ).unop)) =
    TypeCat.ofHom (fun Q : FpSpaceQuotient f F (ofOver U.unop) ↦
      Q.pullback (ofOverMap φ.unop)) ≫
    TypeCat.ofHom (fun Q : FpSpaceQuotient f F (ofOver V.unop) ↦
      Q.pullback (ofOverMap ψ.unop)) := sorry

/-- The finitely presented presheaf on schemes over `S` sending `U` to pairs `(h, Q)`
with `h : ofOver U ⟶ B` and `Q` a kernel-identified finitely presented quasi-coherent
quotient of `F_U` flat over `ofOver U`. -/
def fpOverFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := FpSpaceQuotient f F (ofOver U.unop)
  map {U V} (φ : U ⟶ V) :=
    TypeCat.ofHom fun (Q : FpSpaceQuotient f F (ofOver U.unop)) ↦
      Q.pullback (ofOverMap φ.unop)
  map_id := fpOverFunctor_map_id f F
  map_comp := fpOverFunctor_map_comp f F

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
    (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) : FpSpaceQuotient f F (ofOver U.unop) :=
  Q.pullback (yonedaEquiv.symm x.down)

/-- The pullback comparison for finitely presented quotient pairs is natural in test schemes. -/
theorem toFpSheafHom_naturality (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : FpSpaceQuotient f F T)
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (AlgebraicSpace.toSheaf.obj T).obj.map φ ≫ TypeCat.ofHom (toFpSheafHomApp f F Q V) =
      TypeCat.ofHom (toFpSheafHomApp f F Q U) ≫ (fpOverFunctor f F).map φ := sorry

/-- The canonical morphism of fppf sheaves `T ⟶ Q^{fp}_{F/X/B}` associated to a
finitely presented pair `(h, Q)` over an algebraic space `T`. -/
def toFpSheafHom (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (T : AlgebraicSpace S) (Q : FpSpaceQuotient f F T) :
    (AlgebraicSpace.toSheaf.obj T) ⟶ fpSheaf f F :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toFpSheafHomApp f F Q U)
      naturality {_ _} φ := toFpSheafHom_naturality f F Q φ }

/-- On a scheme `U` over `S`, `toFpSheafHom` evaluates by pullback along the
corresponding morphism `ofOver U ⟶ T`. -/
theorem toFpSheafHom_app (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {T : AlgebraicSpace S} (Q : FpSpaceQuotient f F T) (U : (Over S)ᵒᵖ)
    (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) :
    (toFpSheafHom f F T Q).hom.app U x = toFpSheafHomApp f F Q U x := sorry

/-- Pullback of quotient pairs gives a bijection with morphisms from the sheaf of points
of an algebraic space to the sheaf of quasi-coherent quotients flat over the base. -/
theorem sheafHom_bijective (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (T : AlgebraicSpace S) :
    Function.Bijective (toSheafHom f F T) := sorry

/-- Pullback of finitely presented quotient pairs gives a bijection with morphisms from
the sheaf of points of an algebraic space to the sheaf of finitely presented flat quotients. -/
theorem fpSheafHom_bijective (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (T : AlgebraicSpace S) :
    Function.Bijective (toFpSheafHom f F T) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
