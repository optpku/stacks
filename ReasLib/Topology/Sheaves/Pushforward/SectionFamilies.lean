/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Functors

/-!
# Section families for sheaf pushforward morphisms

Mathlib's `TopCat.Sheaf.pushforward` and its pullback-pushforward adjunction are the canonical
owners of pushforward morphisms. This module provides the complementary sectionwise presentation:
a morphism `𝒢 ⟶ f_*ℱ` is equivalently a family of maps `𝒢(V) ⟶ ℱ(U)` for every
`U ⊆ f⁻¹(V)`, compatible with restriction in both opens. It is useful when a construction is
given on explicitly chosen opens rather than as a natural transformation.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe w v u

namespace TopCat.Presheaf

/-- A collection of maps `G(V) ⟶ F(U)` for opens `U ⊆ f⁻¹(V)`, compatible with restriction maps
in both open-set variables.  This is the presheaf-level data underlying a map into a pushforward.
-/
structure PushforwardHomFamily {X Y : TopCat.{w}} (f : X ⟶ Y)
    {C : Type u} [Category.{v} C] (G : Y.Presheaf C) (F : X.Presheaf C) where
  /-- The map attached to opens `U`, `V` with `U ⊆ f⁻¹(V)`. -/
  app (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f).obj V) :
    G.obj (op V) ⟶ F.obj (op U)
  /-- Compatibility with restriction in the source space of `f`. -/
  source_naturality {U U' : Opens X} {V : Opens Y} (i : U' ⟶ U)
      (h : U ≤ (Opens.map f).obj V) :
    CommSq (app U V h) (𝟙 _) (F.map i.op) (app U' V (i.le.trans h))
  /-- Compatibility with restriction in the target space of `f`. -/
  target_naturality {U : Opens X} {V V' : Opens Y} (j : V ⟶ V')
      (h : U ≤ (Opens.map f).obj V) :
    CommSq (G.map j.op) (app U V' (h.trans ((Opens.map f).map j).le))
      (app U V h) (𝟙 _)

namespace PushforwardHomFamily

variable {X Y : TopCat.{w}} {f : X ⟶ Y}
variable {C : Type u} [Category.{v} C]
variable {G G' : Y.Presheaf C} {F F' : X.Presheaf C}

/-- Two compatible pushforward section families are equal when all of their section components
are equal. -/
@[ext]
theorem ext (η θ : PushforwardHomFamily f G F)
    (h : ∀ (U : Opens X) (V : Opens Y) (hUV : U ≤ (Opens.map f).obj V),
      η.app U V hUV = θ.app U V hUV) :
    η = θ := sorry

/-- The component family determined by a presheaf morphism `G ⟶ f_*F`. -/
def ofHomApp (ξ : G ⟶ (pushforward C f).obj F) (U : Opens X) (V : Opens Y)
    (h : U ≤ (Opens.map f).obj V) : G.obj (op V) ⟶ F.obj (op U) :=
  ξ.app (op V) ≫ F.map (homOfLE h).op

/-- The component family of a pushforward morphism is compatible with restriction in the source
space of `f`. -/
theorem ofHomApp_source_naturality (ξ : G ⟶ (pushforward C f).obj F) :
    ∀ {U U' : Opens X} {V : Opens Y} (i : U' ⟶ U)
      (h : U ≤ (Opens.map f).obj V),
      CommSq (ofHomApp ξ U V h) (𝟙 _) (F.map i.op)
        (ofHomApp ξ U' V (i.le.trans h)) := sorry

/-- The component family of a pushforward morphism is compatible with restriction in the target
space of `f`. -/
theorem ofHomApp_target_naturality (ξ : G ⟶ (pushforward C f).obj F) :
    ∀ {U : Opens X} {V V' : Opens Y} (j : V ⟶ V')
      (h : U ≤ (Opens.map f).obj V),
      CommSq (G.map j.op)
        (ofHomApp ξ U V' (h.trans ((Opens.map f).map j).le))
        (ofHomApp ξ U V h) (𝟙 _) := sorry

/-- Bundle the compatible two-open-set family determined by a presheaf morphism `G ⟶ f_*F`. -/
def ofHom (ξ : G ⟶ (pushforward C f).obj F) : PushforwardHomFamily f G F where
  app := ofHomApp ξ
  source_naturality := ofHomApp_source_naturality ξ
  target_naturality := ofHomApp_target_naturality ξ

/-- Evaluating a compatible family on `U = f⁻¹(V)` is natural in `V`. -/
theorem toHom_naturality (η : PushforwardHomFamily f G F) :
    ∀ ⦃V V' : (Opens Y)ᵒᵖ⦄ (j : V ⟶ V'),
      G.map j ≫ η.app ((Opens.map f).obj (unop V')) (unop V') le_rfl =
        η.app ((Opens.map f).obj (unop V)) (unop V) le_rfl ≫
          ((pushforward C f).obj F).map j := sorry

/-- Recover a presheaf morphism `G ⟶ f_*F` from a compatible family. -/
def toHom (η : PushforwardHomFamily f G F) : G ⟶ (pushforward C f).obj F where
  app := fun V ↦ η.app ((Opens.map f).obj V.unop) V.unop le_rfl
  naturality := toHom_naturality η

/-- Converting a presheaf morphism to a compatible family and back is the identity. -/
theorem toHom_ofHom (ξ : G ⟶ (pushforward C f).obj F) : toHom (ofHom ξ) = ξ := sorry

/-- Converting a compatible family to a presheaf morphism and back is the identity. -/
theorem ofHom_toHom (η : PushforwardHomFamily f G F) : ofHom (toHom η) = η := sorry

/-- The canonical equivalence between morphisms `G ⟶ f_*F` and compatible collections of maps
`G(V) ⟶ F(U)` for opens `U ⊆ f⁻¹(V)`. -/
noncomputable def homEquiv :
    (G ⟶ (pushforward C f).obj F) ≃ PushforwardHomFamily f G F where
  toFun := ofHom
  invFun := toHom
  left_inv := toHom_ofHom
  right_inv := ofHom_toHom

/-- The compatible-family equivalence is natural under precomposition in `G`. -/
theorem homEquiv_naturality_left (α : G' ⟶ G)
    (ξ : G ⟶ (pushforward C f).obj F) (U : Opens X) (V : Opens Y)
    (h : U ≤ (Opens.map f).obj V) :
    (homEquiv (α ≫ ξ)).app U V h = α.app (op V) ≫ (homEquiv ξ).app U V h := sorry

/-- The compatible-family equivalence is natural under postcomposition in `F`. -/
theorem homEquiv_naturality_right (ξ : G ⟶ (pushforward C f).obj F) (β : F ⟶ F')
    (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f).obj V) :
    (homEquiv (ξ ≫ (pushforward C f).map β)).app U V h =
      (homEquiv ξ).app U V h ≫ β.app (op U) := sorry

end PushforwardHomFamily

end TopCat.Presheaf

namespace TopCat.Sheaf

/-- The sheaf-facing view of `Presheaf.PushforwardHomFamily`.  The compatibility data itself is
presheaf-level; sheafhood is needed only to package its associated morphism as a sheaf morphism.
-/
abbrev ContinuousMapSheafMapFamily {X Y : TopCat.{w}} (f : X ⟶ Y)
    {C : Type u} [Category.{v} C] (𝒢 : Y.Sheaf C) (ℱ : X.Sheaf C) :=
  TopCat.Presheaf.PushforwardHomFamily f 𝒢.presheaf ℱ.presheaf

namespace ContinuousMapSheafMapFamily

variable {X Y : TopCat.{w}} {f : X ⟶ Y}
variable {C : Type u} [Category.{v} C]
variable {𝒢 𝒢' : Y.Sheaf C} {ℱ ℱ' : X.Sheaf C}

/-- The component family determined by a morphism `𝒢 ⟶ f_*ℱ`. -/
def ofHomApp (ξ : 𝒢 ⟶ (pushforward C f).obj ℱ) (U : Opens X) (V : Opens Y)
    (h : U ≤ (Opens.map f).obj V) : 𝒢.presheaf.obj (op V) ⟶ ℱ.presheaf.obj (op U) :=
  TopCat.Presheaf.PushforwardHomFamily.ofHomApp ξ.1 U V h

/-- The family `ofHomApp ξ` is compatible with restriction in `X`. -/
theorem ofHomApp_source_naturality (ξ : 𝒢 ⟶ (pushforward C f).obj ℱ) :
    ∀ {U U' : Opens X} {V : Opens Y} (i : U' ⟶ U)
      (h : U ≤ (Opens.map f).obj V),
      CommSq (ofHomApp ξ U V h) (𝟙 _) (ℱ.presheaf.map i.op)
        (ofHomApp ξ U' V (i.le.trans h)) := sorry
/- Proof strategy: unfold `ofHomApp`, reassociate the two restriction maps in `ℱ`, and use
`Functor.map_comp` for the composite inclusion `U' ⟶ U ⟶ f⁻¹(V)`. -/

/-- The family `ofHomApp ξ` is compatible with restriction in `Y`. -/
theorem ofHomApp_target_naturality (ξ : 𝒢 ⟶ (pushforward C f).obj ℱ) :
    ∀ {U : Opens X} {V V' : Opens Y} (j : V ⟶ V')
      (h : U ≤ (Opens.map f).obj V),
      CommSq (𝒢.presheaf.map j.op)
        (ofHomApp ξ U V' (h.trans ((Opens.map f).map j).le))
        (ofHomApp ξ U V h) (𝟙 _) := sorry
/- Proof strategy: apply the naturality square of `ξ.1` at `j.op`, then postcompose with the
restriction from `f⁻¹(V)` to `U`; identify the composite restriction using `Functor.map_comp`. -/

/-- Bundle the compatible two-open-set family determined by a morphism `𝒢 ⟶ f_*ℱ`. -/
def ofHom (ξ : 𝒢 ⟶ (pushforward C f).obj ℱ) :
    ContinuousMapSheafMapFamily f 𝒢 ℱ :=
  TopCat.Presheaf.PushforwardHomFamily.ofHom ξ.1

/-- Evaluating a compatible family on `U = f⁻¹(V)` is natural in `V`. -/
theorem toHom_naturality (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) :
    ∀ ⦃V V' : (Opens Y)ᵒᵖ⦄ (j : V ⟶ V'),
      𝒢.presheaf.map j ≫ η.app ((Opens.map f).obj (unop V')) (unop V') le_rfl =
        η.app ((Opens.map f).obj (unop V)) (unop V) le_rfl ≫
          ((pushforward C f).obj ℱ).presheaf.map j := sorry
/- Proof strategy: first use `η.target_naturality` with `U = f⁻¹(V')`, then use
`η.source_naturality` for the inclusion `f⁻¹(V) ⟶ f⁻¹(V')`; the pushforward restriction map is
definitionally the corresponding restriction map of `ℱ`. -/

/-- Recover a morphism `𝒢 ⟶ f_*ℱ` from a compatible family. -/
def toHom (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) :
    𝒢 ⟶ (pushforward C f).obj ℱ :=
  ObjectProperty.homMk (TopCat.Presheaf.PushforwardHomFamily.toHom η)

/-- Converting a morphism to a compatible family and back is the identity. -/
theorem toHom_ofHom (ξ : 𝒢 ⟶ (pushforward C f).obj ℱ) : toHom (ofHom ξ) = ξ := sorry
/- Proof strategy: use `ObjectProperty.hom_ext`, evaluate at each open `V`, unfold `toHom`,
`ofHom`, and `ofHomApp`, and simplify the restriction along the identity inclusion. -/

/-- Converting a compatible family to a morphism and back is the identity. -/
theorem ofHom_toHom (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) : ofHom (toHom η) = η := sorry
/- Proof strategy: extensionality reduces the equality to each `app U V h`; unfold the conversions
and apply `CommSq.w (η.source_naturality (homOfLE h) le_rfl)`. -/

/-- The canonical equivalence between morphisms `𝒢 ⟶ f_*ℱ` and compatible collections of maps
`𝒢(V) ⟶ ℱ(U)` for opens `U ⊆ f⁻¹(V)`. -/
noncomputable def homEquiv :
    (𝒢 ⟶ (pushforward C f).obj ℱ) ≃ ContinuousMapSheafMapFamily f 𝒢 ℱ where
  toFun := ofHom
  invFun := toHom
  left_inv := toHom_ofHom
  right_inv := ofHom_toHom

/-- The compatible-family equivalence is natural under precomposition in `𝒢`. -/
theorem homEquiv_naturality_left (α : 𝒢' ⟶ 𝒢)
    (ξ : 𝒢 ⟶ (pushforward C f).obj ℱ) (U : Opens X) (V : Opens Y)
    (h : U ≤ (Opens.map f).obj V) :
    (homEquiv (α ≫ ξ)).app U V h = α.1.app (op V) ≫ (homEquiv ξ).app U V h := sorry
/- Proof strategy: unfold `homEquiv`, `ofHom`, and `ofHomApp`; composition of sheaf morphisms is
componentwise, so the result follows by associativity. -/

/-- The compatible-family equivalence is natural under postcomposition in `ℱ`. -/
theorem homEquiv_naturality_right (ξ : 𝒢 ⟶ (pushforward C f).obj ℱ) (β : ℱ ⟶ ℱ')
    (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f).obj V) :
    (homEquiv (ξ ≫ (pushforward C f).map β)).app U V h =
      (homEquiv ξ).app U V h ≫ β.1.app (op U) := sorry
/- Proof strategy: unfold `homEquiv`, `ofHom`, and `ofHomApp`; use the naturality of `β.1` for
`(homOfLE h).op` to commute postcomposition past the restriction map. -/

end ContinuousMapSheafMapFamily

end TopCat.Sheaf
