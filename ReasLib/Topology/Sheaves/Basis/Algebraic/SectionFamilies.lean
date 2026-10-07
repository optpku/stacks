module

public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
public import ReasLib.Topology.Sheaves.Basis.SectionFamilies

/-!
# Extension of algebraic two-basis section families

The data `TopCat.Presheaf.BasisPushforwardHomFamily` is coefficient-category-independent. This module adds the
algebraic-structure and limit-preservation hypotheses needed to extend such a family uniquely to a
morphism into a sheaf pushforward. It is complementary to
`AlgebraicBasisSheaf.existsUnique_pushforwardHom_of_restriction`: that theorem starts from a
single target-basis morphism of restrictions, whereas this one starts from explicit maps on two
independently chosen bases.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

universe w v u u1

namespace TopCat.Presheaf.BasisPushforwardHomFamily

variable {D : Type u} [Category.{v} D]
variable [Limits.HasLimitsOfSize.{w, w} D]

/-- A compatible family on independently chosen bases of the source and target spaces extends
uniquely to a morphism from the target sheaf to the pushforward of the source sheaf. -/
theorem existsUniquePushforwardHom
    {Forget : D ⥤ Type u1} [IsAlgebraicStructure D Forget]
    [Limits.PreservesLimitsOfSize.{w, w} Forget]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf) :
    ∃! Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ,
      ∀ (U : BasisOpen BX) (V : BasisOpen BY)
        (h : U.obj ≤ (Opens.map f).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h := sorry

/-- Extend a compatible two-basis section family to its uniquely determined sheaf morphism into
the pushforward. -/
noncomputable def toHom
    {Forget : D ⥤ Type u1} [IsAlgebraicStructure D Forget]
    [Limits.PreservesLimitsOfSize.{w, w} Forget]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf) :
    𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ :=
  Classical.choose (ExistsUnique.exists
    (existsUniquePushforwardHom (Forget := Forget) f hBX hBY φ))

/-- The morphism selected by `toHom` restricts to the prescribed family on both bases. -/
theorem toHom_app
    {Forget : D ⥤ Type u1} [IsAlgebraicStructure D Forget]
    [Limits.PreservesLimitsOfSize.{w, w} Forget]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (U : BasisOpen BX) (V : BasisOpen BY)
    (h : U.obj ≤ (Opens.map f).obj V.obj) :
    (toHom (Forget := Forget) f hBX hBY φ).hom.app (op V.obj) ≫
      ℱ.presheaf.map (homOfLE h).op =
      φ.app U V h := sorry

/-- A morphism whose two-basis components equal `φ` is the canonical extension `toHom f hBX hBY
φ`. -/
theorem toHom_unique
    {Forget : D ⥤ Type u1} [IsAlgebraicStructure D Forget]
    [Limits.PreservesLimitsOfSize.{w, w} Forget]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ)
    (hΦ : ∀ (U : BasisOpen BX) (V : BasisOpen BY)
      (h : U.obj ≤ (Opens.map f).obj V.obj),
      Φ.hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h) :
    Φ = toHom (Forget := Forget) f hBX hBY φ := sorry

/-- Extending the basis restriction of a sheaf morphism recovers that morphism. -/
@[simp]
theorem toHom_ofHom
    {Forget : D ⥤ Type u1} [IsAlgebraicStructure D Forget]
    [Limits.PreservesLimitsOfSize.{w, w} Forget]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ) :
    toHom (Forget := Forget) f hBX hBY (ofHom f Φ) = Φ := sorry

/-- Restricting the extension of a compatible two-basis family recovers that family. -/
@[simp]
theorem ofHom_toHom
    {Forget : D ⥤ Type u1} [IsAlgebraicStructure D Forget]
    [Limits.PreservesLimitsOfSize.{w, w} Forget]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf) :
    ofHom f (toHom (Forget := Forget) f hBX hBY φ) = φ := sorry

/-- The canonical equivalence between morphisms into a pushforward and compatible section
families on two bases. -/
noncomputable def homEquiv
    {Forget : D ⥤ Type u1} [IsAlgebraicStructure D Forget]
    [Limits.PreservesLimitsOfSize.{w, w} Forget]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {BX : Set (Opens X)} {BY : Set (Opens Y)}
    {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY) :
    (𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ) ≃
      BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf where
  toFun := ofHom f
  invFun := toHom (Forget := Forget) f hBX hBY
  left_inv := toHom_ofHom (Forget := Forget) f hBX hBY
  right_inv := ofHom_toHom (Forget := Forget) f hBX hBY

end TopCat.Presheaf.BasisPushforwardHomFamily
