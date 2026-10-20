/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
public import ReasLib.Topology.Sheaves.Basis.Cover
public import ReasLib.Topology.Sheaves.Basis.SectionFamilies

/-!
# Extension of two-basis section families

A `TopCat.Presheaf.BasisPushforwardHomFamily` records maps `𝒢(V) ⟶ ℱ(U)` for basis opens
`V` of `Y` and `U ⊆ f⁻¹(V)` of `X`. This module constructs the morphism `𝒢 ⟶ f_*ℱ` it
determines:

* over a basis open `V` of `Y`, the components `𝒢(V) ⟶ ℱ(U)` are glued along the cover of
  `f⁻¹(V)` by basis opens of `X` (`preimageApp`), using the sheaf condition of `ℱ`;
* these glued maps form a morphism between the restrictions of `𝒢` and `f_*ℱ` to the basis
  `BY` (`basisHom`), which extends uniquely along the cover-dense inclusion of basis opens
  (`toHom`).

Only the categorical sheaf conditions of `ℱ` and `f_*ℱ` are used, so no algebraic-structure or
limit hypotheses on the coefficient category are needed; for a type of algebraic structures this
specializes to the classical statement. It is complementary to
`AlgebraicBasisSheaf.existsUnique_pushforwardHom_of_restriction`: that theorem starts from a
single target-basis morphism of restrictions, whereas this one starts from explicit maps on two
independently chosen bases.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

universe w v u

/-- The basis opens of `B` contained in an open `W` cover `W`. -/
theorem TopologicalSpace.Opens.ofArrows_basisOpen_le_mem_grothendieckTopology
    {X : Type w} [TopologicalSpace X] {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (W : Opens X) :
    Sieve.ofArrows (fun U : {U : BasisOpen B // U.obj ≤ W} ↦ U.1.obj)
        (fun U ↦ homOfLE U.2) ∈ Opens.grothendieckTopology X W := by
  intro x hx
  obtain ⟨U, hUB, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  let U' : {U : BasisOpen B // U.obj ≤ W} := ⟨⟨U, hUB⟩, hUW⟩
  exact ⟨U, homOfLE hUW, Sieve.ofArrows_mk _ (fun U : {U : BasisOpen B // U.obj ≤ W} ↦ homOfLE U.2) U', hxU⟩

namespace TopCat.Presheaf.BasisPushforwardHomFamily

variable {D : Type u} [Category.{v} D]
variable {X Y : TopCat.{w}} {f : X ⟶ Y}
variable {BX : Set (Opens X)} {BY : Set (Opens Y)}
variable {𝒢 : Y.Sheaf D} {ℱ : X.Sheaf D}

/-- For a fixed basis open `V` of `Y`, the components `φ.app U V` over basis opens
`U ⊆ f⁻¹(V)` agree on overlaps. -/
theorem app_compatible (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (hBX : Opens.IsBasis BX) (V : BasisOpen BY) :
    ∀ ⦃W : Opens X⦄ ⦃U U' : {U : BasisOpen BX // U.obj ≤ (Opens.map f).obj V.obj}⦄
      (a : W ⟶ U.1.obj) (b : W ⟶ U'.1.obj),
      a ≫ homOfLE U.2 = b ≫ homOfLE U'.2 →
        φ.app U.1 V U.2 ≫ ℱ.presheaf.map a.op = φ.app U'.1 V U'.2 ≫ ℱ.presheaf.map b.op := by
  intro W U U' a b _
  refine ℱ.property.hom_ext_ofArrows _
    (Opens.ofArrows_basisOpen_le_mem_grothendieckTopology hBX W) fun T ↦ ?_
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
  have hT : ∀ {U₀ : BasisOpen BX} (c : W ⟶ U₀.obj), homOfLE T.2 ≫ c =
      (ObjectProperty.homMk (homOfLE (T.2.trans c.le)) : T.1 ⟶ U₀).hom :=
    fun _ ↦ Subsingleton.elim _ _
  rw [hT a, hT b, φ.source_naturality, φ.source_naturality]

/-- The section map `𝒢(V) ⟶ ℱ(f⁻¹(V))` over a basis open `V` of `Y`, glued from the components
`φ.app U V` along the cover of `f⁻¹(V)` by basis opens of `X`. -/
noncomputable def preimageApp (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (hBX : Opens.IsBasis BX) (V : BasisOpen BY) :
    𝒢.presheaf.obj (op V.obj) ⟶ ℱ.presheaf.obj (op ((Opens.map f).obj V.obj)) :=
  ℱ.property.amalgamateOfArrows (fun U ↦ homOfLE U.2)
    (Opens.ofArrows_basisOpen_le_mem_grothendieckTopology hBX _)
    (fun U ↦ φ.app U.1 V U.2) (φ.app_compatible hBX V)

/-- Restricting the glued section map over `f⁻¹(V)` to a basis open `U` recovers `φ.app U V`. -/
@[reassoc (attr := simp)]
theorem preimageApp_restrict (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (hBX : Opens.IsBasis BX) (U : BasisOpen BX) (V : BasisOpen BY)
    (h : U.obj ≤ (Opens.map f).obj V.obj) :
    φ.preimageApp hBX V ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h :=
  ℱ.property.amalgamateOfArrows_map (fun U : {U : BasisOpen BX // U.obj ≤ (Opens.map f).obj V.obj} ↦
      homOfLE U.2) (Opens.ofArrows_basisOpen_le_mem_grothendieckTopology hBX _)
    (fun U ↦ φ.app U.1 V U.2) (φ.app_compatible hBX V) ⟨U, h⟩

/-- A map `𝒢(V) ⟶ ℱ(f⁻¹(V))` is determined by its restrictions to basis opens `U ⊆ f⁻¹(V)`. -/
theorem hom_ext_preimage (hBX : Opens.IsBasis BX) {E : D} (V : Opens Y)
    {s t : E ⟶ ℱ.presheaf.obj (op ((Opens.map f).obj V))}
    (h : ∀ (U : BasisOpen BX) (hUV : U.obj ≤ (Opens.map f).obj V),
      s ≫ ℱ.presheaf.map (homOfLE hUV).op = t ≫ ℱ.presheaf.map (homOfLE hUV).op) :
    s = t :=
  ℱ.property.hom_ext_ofArrows _ (Opens.ofArrows_basisOpen_le_mem_grothendieckTopology hBX _)
    fun U ↦ h U.1 U.2

/-- The glued section maps are natural in the basis open `V` of `Y`. -/
theorem preimageApp_naturality
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (hBX : Opens.IsBasis BX) {V V' : BasisOpen BY} (j : V ⟶ V') :
    𝒢.presheaf.map j.hom.op ≫ φ.preimageApp hBX V =
      φ.preimageApp hBX V' ≫ ℱ.presheaf.map ((Opens.map f).map j.hom).op := by
  refine hom_ext_preimage hBX V.obj fun U hUV ↦ ?_
  rw [Category.assoc, preimageApp_restrict, φ.target_naturality, Category.assoc,
    ← Functor.map_comp, ← op_comp]
  exact (φ.preimageApp_restrict hBX U V' _).symm.trans (by congr 3)

/-- The morphism between the restrictions of `𝒢` and `f_*ℱ` to the basis `BY` whose component
over `V` is the glued map `preimageApp φ hBX V`. -/
noncomputable def basisHom (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (hBX : Opens.IsBasis BX) :
    (basisOpenInclusion BY).op ⋙ 𝒢.presheaf ⟶
      (basisOpenInclusion BY).op ⋙ ((TopCat.Sheaf.pushforward D f).obj ℱ).presheaf where
  app V := φ.preimageApp hBX V.unop
  naturality _ _ j := φ.preimageApp_naturality hBX j.unop

variable (f)

/-- Extend a compatible two-basis section family to a sheaf morphism into the pushforward:
the glued basis morphism `basisHom φ hBX` is extended along the cover-dense inclusion of the
basis opens of `Y`. -/
noncomputable def toHom
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf) :
    𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ :=
  -- Local instance justification (defeq pin): cover density is determined by the explicit
  -- basis proof `hBY`; it is not a global instance.
  letI : (basisOpenInclusion BY).IsCoverDense (Opens.grothendieckTopology Y) :=
    basisOpenInclusion_isCoverDense hBY
  ObjectProperty.homMk (Functor.IsCoverDense.sheafHom (φ.basisHom hBX))

/-- On a basis open `V` of `Y`, the extension `toHom` is the glued map `preimageApp`. -/
theorem toHom_app_basisOpen
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf) (V : BasisOpen BY) :
    (toHom f hBX hBY φ).hom.app (op V.obj) = φ.preimageApp hBX V := by
  letI : (basisOpenInclusion BY).IsCoverDense (Opens.grothendieckTopology Y) :=
    basisOpenInclusion_isCoverDense hBY
  exact congr_app (Functor.IsCoverDense.sheafHom_restrict_eq (φ.basisHom hBX)) (op V)

/-- The morphism `toHom` restricts to the prescribed family on both bases. -/
@[simp]
theorem toHom_app
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (U : BasisOpen BX) (V : BasisOpen BY)
    (h : U.obj ≤ (Opens.map f).obj V.obj) :
    (toHom f hBX hBY φ).hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h := by
  rw [toHom_app_basisOpen]
  exact φ.preimageApp_restrict hBX U V h

/-- A morphism whose two-basis components equal `φ` is the extension `toHom f hBX hBY φ`. -/
theorem toHom_unique
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf)
    (Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ)
    (hΦ : ∀ (U : BasisOpen BX) (V : BasisOpen BY)
      (h : U.obj ≤ (Opens.map f).obj V.obj),
      Φ.hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h) :
    Φ = toHom f hBX hBY φ := by
  letI : (basisOpenInclusion BY).IsCoverDense (Opens.grothendieckTopology Y) :=
    basisOpenInclusion_isCoverDense hBY
  have hrestr : Functor.whiskerLeft (basisOpenInclusion BY).op Φ.hom = φ.basisHom hBX := by
    ext V
    exact hom_ext_preimage hBX V.unop.obj fun U hUV ↦
      (hΦ U V.unop hUV).trans (φ.preimageApp_restrict hBX U V.unop hUV).symm
  refine ObjectProperty.hom_ext _ ?_
  change Φ.hom = Functor.IsCoverDense.sheafHom (φ.basisHom hBX)
  rw [← hrestr, Functor.IsCoverDense.sheafHom_eq]

/-- A compatible family on independently chosen bases of the source and target spaces extends
uniquely to a morphism from the target sheaf to the pushforward of the source sheaf. -/
theorem existsUniquePushforwardHom
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf) :
    ∃! Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ,
      ∀ (U : BasisOpen BX) (V : BasisOpen BY)
        (h : U.obj ≤ (Opens.map f).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h :=
  ⟨toHom f hBX hBY φ, toHom_app f hBX hBY φ, toHom_unique f hBX hBY φ⟩

/-- Extending the basis restriction of a sheaf morphism recovers that morphism. -/
@[simp]
theorem toHom_ofHom
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ) :
    toHom f hBX hBY (ofHom f Φ) = Φ :=
  (toHom_unique f hBX hBY _ Φ fun U V h ↦ (ofHom_app f Φ U V h).symm).symm

/-- Restricting the extension of a compatible two-basis family recovers that family. -/
@[simp]
theorem ofHom_toHom
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf) :
    ofHom f (toHom f hBX hBY φ) = φ :=
  ext _ _ _ _ _ _ _ fun U V h ↦ (ofHom_app f _ U V h).trans (toHom_app f hBX hBY φ U V h)

/-- The canonical equivalence between morphisms into a pushforward and compatible section
families on two bases. -/
noncomputable def homEquiv
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY) :
    (𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ) ≃
      BasisPushforwardHomFamily f BX BY 𝒢.presheaf ℱ.presheaf where
  toFun := ofHom f
  invFun := toHom f hBX hBY
  left_inv := toHom_ofHom f hBX hBY
  right_inv := ofHom_toHom f hBX hBY

end TopCat.Presheaf.BasisPushforwardHomFamily
