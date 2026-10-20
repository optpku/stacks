module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SpaceHom

/-!
# The Hom functor of quasi-coherent modules as an fppf sheaf on Sch/S

This module realises `Hom(F, G)` as an fppf sheaf on `Over S`, and constructs
the canonical comparison from space-level Hom pairs to morphisms of sheaves
out of an algebraic space `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Restricting Hom pairs along the identity of a test scheme is the identity map. -/
private theorem overFunctor_map_id (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (U : (Over S)ᵒᵖ) :
    TypeCat.ofHom (fun (p : SpaceHom f F G (ofOver U.unop)) ↦
      p.pullback (ofOverMap (𝟙 U).unop)) = 𝟙 (SpaceHom f F G (ofOver U.unop)) :=
  sorry

/-- Restricting Hom pairs along a composite of test-scheme maps is successive restriction. -/
private theorem overFunctor_map_comp (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {U V W : (Over S)ᵒᵖ}
    (φ : U ⟶ V) (ψ : V ⟶ W) :
    TypeCat.ofHom (fun (p : SpaceHom f F G (ofOver U.unop)) ↦
      p.pullback (ofOverMap (φ ≫ ψ).unop)) =
    TypeCat.ofHom (fun (p : SpaceHom f F G (ofOver U.unop)) ↦
      p.pullback (ofOverMap φ.unop)) ≫
    TypeCat.ofHom (fun (p : SpaceHom f F G (ofOver V.unop)) ↦
      p.pullback (ofOverMap ψ.unop)) :=
  sorry

/-- The presheaf on schemes over `S` sending `U` to pairs `(h, u)` with
`h : ofOver U ⟶ B` and `u : F_U ⟶ G_U` an `𝒪_{X_U}`-module map. -/
def overFunctor (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := SpaceHom f F G (ofOver U.unop)
  map {U V} φ :=
    TypeCat.ofHom fun (p : SpaceHom f F G (ofOver U.unop)) ↦
      p.pullback (ofOverMap φ.unop)
  map_id := by exact overFunctor_map_id f F G
  map_comp := by exact overFunctor_map_comp f F G

/-- Evaluating `overFunctor` at a scheme over `S` recovers space-level Hom pairs. -/
theorem overFunctor_obj (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : Over S) :
    (overFunctor f F G).obj (op U) = SpaceHom f F G (ofOver U) :=
  sorry

/-- The presheaf `overFunctor f F G` is an fppf sheaf on `Over S`. -/
theorem overFunctor_isSheaf (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (overFunctor f F G) :=
  sorry

/-- The fppf sheaf `Hom(F, G)` on `(Sch/S)_fppf`. -/
def homSheaf (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨overFunctor f F G, overFunctor_isSheaf f F G⟩

/-- Evaluating `homSheaf f F G` at a scheme `U` over `S` recovers space-level Hom
pairs on `ofOver U`. -/
theorem homSheaf_obj (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : Over S) :
    (homSheaf f F G).obj.obj (op U) = SpaceHom f F G (ofOver U) :=
  sorry

/-- The component of the canonical comparison at a scheme `U` over `S`, sending a
`U`-point of `T` to the pullback pair `(h ∘ a, a^* u)`. -/
def toSheafHomApp (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {T : AlgebraicSpace S} (p : SpaceHom f F G T)
    (U : (Over S)ᵒᵖ) (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) :
    SpaceHom f F G (ofOver U.unop) :=
  p.pullback (yonedaEquiv.symm x.down)

/-- Restriction of the sheaf of points commutes with restriction of a fixed Hom pair. -/
private theorem toSheafHom_naturality (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {T : AlgebraicSpace S}
    (p : SpaceHom f F G T) {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (AlgebraicSpace.toSheaf.obj T).obj.map φ ≫
        TypeCat.ofHom (toSheafHomApp f F G p V) =
      TypeCat.ofHom (toSheafHomApp f F G p U) ≫ (overFunctor f F G).map φ :=
  sorry

/-- The canonical morphism of fppf sheaves `T ⟶ Hom(F, G)` associated to a pair
`(h, u)` over an algebraic space `T`. -/
def toSheafHom (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (T : AlgebraicSpace S) (p : SpaceHom f F G T) :
    AlgebraicSpace.toSheaf.obj T ⟶ homSheaf f F G :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toSheafHomApp f F G p U)
      naturality := by exact fun _ _ φ ↦ toSheafHom_naturality f F G p φ }

/-- On a scheme `U` over `S`, `toSheafHom` evaluates by pullback along the
corresponding morphism `ofOver U ⟶ T`. -/
theorem toSheafHom_app (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {T : AlgebraicSpace S} (p : SpaceHom f F G T)
    (U : (Over S)ᵒᵖ) (x : (AlgebraicSpace.toSheaf.obj T).obj.obj U) :
    (toSheafHom f F G T p).hom.app U x = toSheafHomApp f F G p U x :=
  sorry

/-- The component of the situation morphism `Hom(F, G) ⟶ B` at a scheme `U` over
`S`, sending a pair `(h, u)` to the `U`-point of `B` determined by `h`. -/
def homSheafToBaseApp (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : (Over S)ᵒᵖ)
    (p : SpaceHom f F G (ofOver U.unop)) : (AlgebraicSpace.toSheaf.obj B).obj.obj U :=
  ⟨yonedaEquiv (p.hom : yoneda.obj U.unop ⟶ B.functorOfPoints)⟩

/-- Projecting a Hom pair to its base morphism commutes with restriction of test schemes. -/
private theorem homSheafToBase_naturality (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (overFunctor f F G).map φ ≫ TypeCat.ofHom (homSheafToBaseApp f F G V) =
      TypeCat.ofHom (homSheafToBaseApp f F G U) ≫
        (AlgebraicSpace.toSheaf.obj B).obj.map φ :=
  sorry

/-- The situation morphism `Hom(F, G) ⟶ B` of fppf sheaves on `(Sch/S)_fppf`,
sending a pair `(h, u)` to `h`. -/
def homSheafToBase (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : homSheaf f F G ⟶ AlgebraicSpace.toSheaf.obj B :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (homSheafToBaseApp f F G U)
      naturality := by exact fun _ _ φ ↦ homSheafToBase_naturality f F G φ }

/-- On a scheme `U` over `S`, `homSheafToBase` evaluates by sending a pair to its
structural morphism `h`. -/
theorem homSheafToBase_app (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : (Over S)ᵒᵖ)
    (p : SpaceHom f F G (ofOver U.unop)) :
    (homSheafToBase f F G).hom.app U p = homSheafToBaseApp f F G U p :=
  sorry

/-- For any algebraic space `T` over `S`, the canonical pullback construction
identifies pairs consisting of `h : T ⟶ B` and a module morphism `F_T ⟶ G_T`
on `X ×_{B,h} T` with morphisms from the fppf sheaf of points of `T` to `Hom(F, G)`. -/
theorem sheafHom_bijective (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (T : AlgebraicSpace S) :
    Function.Bijective (toSheafHom f F G T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
