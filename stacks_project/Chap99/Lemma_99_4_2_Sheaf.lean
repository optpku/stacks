module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap99.Lemma_99_3_3_Sheaf
public import stacks_project.Chap99.Lemma_99_4_2_SpaceIsom

/-!
# The Isom functor of quasi-coherent modules as an fppf sheaf on Sch/S

This module realises `Isom(F, G)` as an fppf sheaf on `Over S`, and constructs
the canonical comparison from space-level invertible pairs to morphisms of
sheaves out of an algebraic space `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The presheaf on schemes over `S` sending `U` to pairs `(h, u)` with
`h : ofOver U ⟶ B` and `u : F_U ⟶ G_U` an `𝒪_{X_U}`-module isomorphism. -/
def isomOverFunctor (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := SpaceIsom f F G (ofOver U.unop)
  map {U V} φ :=
    TypeCat.ofHom fun (p : SpaceIsom f F G (ofOver U.unop)) ↦
      p.pullback (ofOverMap φ.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating `isomOverFunctor` at a scheme over `S` recovers space-level Isom
pairs. -/
theorem isomOverFunctor_obj (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : Over S) :
    (isomOverFunctor f F G).obj (op U) = SpaceIsom f F G (ofOver U) :=
  sorry

/-- The presheaf `isomOverFunctor f F G` is an fppf sheaf on `Over S`. -/
theorem isomOverFunctor_isSheaf (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (isomOverFunctor f F G) :=
  sorry

/-- The fppf sheaf `Isom(F, G)` on `(Sch/S)_fppf`. -/
def isomSheaf (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨isomOverFunctor f F G, isomOverFunctor_isSheaf f F G⟩

/-- Evaluating `isomSheaf f F G` at a scheme `U` over `S` recovers space-level
Isom pairs on `ofOver U`. -/
theorem isomSheaf_obj (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : Over S) :
    (isomSheaf f F G).obj.obj (op U) = SpaceIsom f F G (ofOver U) :=
  sorry

/-- The component of the canonical comparison at a scheme `U` over `S`, sending a
`U`-point of `T` to the pulled-back invertible pair `(h ∘ a, a^* u)`. -/
def toSheafIsomApp (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {T : AlgebraicSpace S} (p : SpaceIsom f F G T)
    (U : (Over S)ᵒᵖ) (x : (uliftFunctorOfPoints T).obj U) :
    SpaceIsom f F G (ofOver U.unop) :=
  p.pullback (yonedaEquiv.symm x.down)

/-- The canonical morphism of fppf sheaves `T ⟶ Isom(F, G)` associated to an
invertible pair `(h, u)` over an algebraic space `T`. -/
def toSheafIsom (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (T : AlgebraicSpace S) (p : SpaceIsom f F G T) :
    uliftSheafOfPoints T ⟶ isomSheaf f F G :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (toSheafIsomApp f F G p U)
      naturality := sorry }

/-- On a scheme `U` over `S`, `toSheafIsom` evaluates by pullback along the
corresponding morphism `ofOver U ⟶ T`. -/
theorem toSheafIsom_app (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {T : AlgebraicSpace S} (p : SpaceIsom f F G T)
    (U : (Over S)ᵒᵖ) (x : (uliftFunctorOfPoints T).obj U) :
    (toSheafIsom f F G T p).hom.app U x = toSheafIsomApp f F G p U x :=
  sorry

/-- The component of the inclusion `Isom(F, G) ⟶ Hom(F, G)` at a scheme `U` over
`S`, sending an invertible pair to its underlying Hom pair. -/
def isomSheafToHomApp (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : (Over S)ᵒᵖ)
    (q : SpaceIsom f F G (ofOver U.unop)) : SpaceHom f F G (ofOver U.unop) :=
  q.toSpaceHom

/-- The inclusion of fppf sheaves `Isom(F, G) ⟶ Hom(F, G)` on `(Sch/S)_fppf`,
sending an invertible pair `(h, u)` to the same pair as a Hom section. -/
def isomSheafToHom (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : isomSheaf f F G ⟶ homSheaf f F G :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom (isomSheafToHomApp f F G U)
      naturality := sorry }

/-- On a scheme `U` over `S`, `isomSheafToHom` evaluates by forgetting
invertibility. -/
theorem isomSheafToHom_app (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : (Over S)ᵒᵖ)
    (q : SpaceIsom f F G (ofOver U.unop)) :
    (isomSheafToHom f F G).hom.app U q = isomSheafToHomApp f F G U q :=
  sorry

/-- The comparison `T ⟶ Isom(F, G)` composed with the inclusion into `Hom(F, G)`
recovers the Hom comparison of the underlying pair. -/
theorem toSheafIsom_comp_isomSheafToHom (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {T : AlgebraicSpace S}
    (p : SpaceIsom f F G T) :
    toSheafIsom f F G T p ≫ isomSheafToHom f F G =
      toSheafHom f F G T p.toSpaceHom :=
  sorry

/-- The situation morphism `Isom(F, G) ⟶ B` of fppf sheaves on `(Sch/S)_fppf`,
sending an invertible pair `(h, u)` to `h`. -/
def isomSheafToBase (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : isomSheaf f F G ⟶ uliftSheafOfPoints B :=
  isomSheafToHom f F G ≫ homSheafToBase f F G

/-- The situation morphism `Isom(F, G) ⟶ B` is the Hom situation morphism after
the inclusion of invertible pairs. -/
theorem isomSheafToBase_eq (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] :
    isomSheafToBase f F G = isomSheafToHom f F G ≫ homSheafToBase f F G :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
