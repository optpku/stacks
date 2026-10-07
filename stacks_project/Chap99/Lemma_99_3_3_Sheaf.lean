module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap97.Lemma_97_11_4_RelativeHom
public import stacks_project.Chap99.Lemma_99_3_3_SpaceHom

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

/-- The presheaf on schemes over `S` sending `U` to pairs `(h, u)` with
`h : ofOver U ⟶ B` and `u : F_U ⟶ G_U` an `𝒪_{X_U}`-module map. -/
def overFunctor (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := SpaceHom f F G (ofOver U.unop)
  map {U V} φ :=
    TypeCat.ofHom fun (p : SpaceHom f F G (ofOver U.unop)) ↦
      p.pullback (ofOverMap φ.unop)
  map_id := sorry
  map_comp := sorry

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
    (U : (Over S)ᵒᵖ) (x : (uliftFunctorOfPoints T).obj U) :
    SpaceHom f F G (ofOver U.unop) :=
  p.pullback (yonedaEquiv.symm x.down)

/-- The canonical morphism of fppf sheaves `T ⟶ Hom(F, G)` associated to a pair
`(h, u)` over an algebraic space `T`. -/
def toSheafHom (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (T : AlgebraicSpace S) (p : SpaceHom f F G T) :
    uliftSheafOfPoints T ⟶ homSheaf f F G :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toSheafHomApp f F G p U)
      naturality := sorry }

/-- On a scheme `U` over `S`, `toSheafHom` evaluates by pullback along the
corresponding morphism `ofOver U ⟶ T`. -/
theorem toSheafHom_app (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {T : AlgebraicSpace S} (p : SpaceHom f F G T)
    (U : (Over S)ᵒᵖ) (x : (uliftFunctorOfPoints T).obj U) :
    (toSheafHom f F G T p).hom.app U x = toSheafHomApp f F G p U x :=
  sorry

/-- The component of the situation morphism `Hom(F, G) ⟶ B` at a scheme `U` over
`S`, sending a pair `(h, u)` to the `U`-point of `B` determined by `h`. -/
def homSheafToBaseApp (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : (Over S)ᵒᵖ)
    (p : SpaceHom f F G (ofOver U.unop)) : (uliftFunctorOfPoints B).obj U :=
  ⟨yonedaEquiv (p.hom : yoneda.obj U.unop ⟶ B.functorOfPoints)⟩

/-- The situation morphism `Hom(F, G) ⟶ B` of fppf sheaves on `(Sch/S)_fppf`,
sending a pair `(h, u)` to `h`. -/
def homSheafToBase (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : homSheaf f F G ⟶ uliftSheafOfPoints B :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (homSheafToBaseApp f F G U)
      naturality := sorry }

/-- On a scheme `U` over `S`, `homSheafToBase` evaluates by sending a pair to its
structural morphism `h`. -/
theorem homSheafToBase_app (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : (Over S)ᵒᵖ)
    (p : SpaceHom f F G (ofOver U.unop)) :
    (homSheafToBase f F G).hom.app U p = homSheafToBaseApp f F G U p :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
