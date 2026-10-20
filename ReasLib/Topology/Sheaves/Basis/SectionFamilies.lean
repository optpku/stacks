module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Topology.Sheaves.Basis.Basic
public import ReasLib.Topology.Sheaves.Pushforward.SectionFamilies

/-!
# Two-basis section families for sheaf pushforward morphisms

This module contains the coefficient-category-independent data of a sectionwise presentation of a
morphism into a sheaf pushforward. A family is indexed by independently chosen bases in the source
and target spaces and records maps on every pair `U ⊆ f⁻¹(V)`, together with both restriction
compatibilities. Algebraic hypotheses are deliberately absent here; the corresponding extension
theorem is owned by `Basis.Algebraic.SectionFamilies`.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

universe w v u

variable {C : Type u} [Category.{v} C]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable (BX : Set (Opens X)) (BY : Set (Opens Y))
variable (G : (Opens Y)ᵒᵖ ⥤ C) (F : (Opens X)ᵒᵖ ⥤ C)

namespace TopCat.Presheaf

/-- A family of morphisms from sections of `G` on basis opens of `Y` to sections of `F` on
basis opens of `X` mapping into them, compatible with restriction in both variables. -/
structure BasisPushforwardHomFamily where
  /-- The section morphism associated to `U ⊆ f⁻¹(V)`. -/
  app (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj) :
    G.obj (op V.obj) ⟶ F.obj (op U.obj)
  /-- Compatibility with restriction between basis opens of `X`. -/
  source_naturality {U U' : BasisOpen BX} (i : U' ⟶ U) {V : BasisOpen BY}
      (h : U.obj ≤ (Opens.map f).obj V.obj) :
    app U V h ≫ F.map i.hom.op = app U' V (i.hom.le.trans h)
  /-- Compatibility with restriction between basis opens of `Y`. -/
  target_naturality {U : BasisOpen BX} {V V' : BasisOpen BY} (j : V ⟶ V')
      (h : U.obj ≤ (Opens.map f).obj V.obj) :
    G.map j.hom.op ≫ app U V h =
      app U V' (h.trans ((Opens.map f).map j.hom).le)

namespace BasisPushforwardHomFamily

/-- Two compatible two-basis section families are equal when all of their section components
are equal. -/
@[ext]
theorem ext (η θ : BasisPushforwardHomFamily f BX BY G F)
    (h : ∀ (U : BasisOpen BX) (V : BasisOpen BY)
      (hUV : U.obj ≤ (Opens.map f).obj V.obj), η.app U V hUV = θ.app U V hUV) :
    η = θ := sorry

/-- The restriction to two chosen bases of the section family induced by a morphism into a
presheaf pushforward. -/
def ofPresheafHom
    {X Y : TopCat.{w}} {C : Type u} [Category.{v} C]
    (f : X ⟶ Y) {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {G : (Opens Y)ᵒᵖ ⥤ C} {F : (Opens X)ᵒᵖ ⥤ C}
    (ξ : G ⟶ (TopCat.Presheaf.pushforward C f).obj F) :
    BasisPushforwardHomFamily f BX BY G F where
  app U V h := (TopCat.Presheaf.PushforwardHomFamily.ofHom ξ).app U.obj V.obj h
  source_naturality := sorry
  target_naturality := sorry

/-- A component of `ofPresheafHom` is the usual restriction of the corresponding pushforward
morphism. -/
@[simp]
theorem ofPresheafHom_app
    {X Y : TopCat.{w}} {C : Type u} [Category.{v} C]
    (f : X ⟶ Y) {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {G : (Opens Y)ᵒᵖ ⥤ C} {F : (Opens X)ᵒᵖ ⥤ C}
    (ξ : G ⟶ (TopCat.Presheaf.pushforward C f).obj F)
    (U : BasisOpen BX) (V : BasisOpen BY)
    (h : U.obj ≤ (Opens.map f).obj V.obj) :
    (ofPresheafHom f ξ).app U V h =
      ξ.app (op V.obj) ≫ F.map (homOfLE h).op := sorry

/-- The two-basis family obtained by restricting a morphism of sheaves into a pushforward. -/
def ofHom
    {X Y : TopCat.{w}} {D : Type u} [Category.{v} D]
    (f : X ⟶ Y) {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ) :
    BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf :=
  ofPresheafHom f Φ.hom

/-- The components of `ofHom` are the section maps obtained by restricting the pushforward
morphism. -/
@[simp]
theorem ofHom_app
    {X Y : TopCat.{w}} {D : Type u} [Category.{v} D]
    (f : X ⟶ Y) {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ)
    (U : BasisOpen BX) (V : BasisOpen BY)
    (h : U.obj ≤ (Opens.map f).obj V.obj) :
    (ofHom f Φ).app U V h =
      Φ.hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op := sorry

end BasisPushforwardHomFamily

end TopCat.Presheaf
