module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Open-cover criteria for flat scheme morphisms

This leaf packages the local-on-open-cover and affine-section forms of
mathlib's canonical `AlgebraicGeometry.Flat` morphism property.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

set_option linter.checkUnivs false in
/-- Open-cover data witnessing flatness of a scheme morphism. -/
structure FlatOpenCover
    (f : X ⟶ S) where
  /-- The indexing type for target opens. -/
  J : Type v
  /-- The target open cover. -/
  V : J → S.Opens
  /-- The target opens cover `S`. -/
  iSup_eq_top : (⨆ j, V j) = ⊤
  /-- The indexing type for source opens over each target open. -/
  I : J → Type w
  /-- The source open cover over each target open. -/
  U : ∀ j, I j → X.Opens
  /-- The source opens cover the inverse image of the corresponding target open. -/
  iSup_eq_preimage : ∀ j, (⨆ i, U j i) = f ⁻¹ᵁ V j
  /-- Every restricted morphism is flat. -/
  flat_resLE : ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, Flat (f.resLE (V j) (U j i) e)

set_option linter.checkUnivs false in
/-- Affine-open-cover data witnessing flatness of a scheme morphism. -/
structure FlatAffineOpenCover
    (f : X ⟶ S) where
  /-- The indexing type for target affine opens. -/
  J : Type v
  /-- The target affine open cover. -/
  V : J → S.Opens
  /-- The target affine opens cover `S`. -/
  iSup_eq_top : (⨆ j, V j) = ⊤
  /-- Every target member is affine. -/
  affine_V : ∀ j, IsAffineOpen (V j)
  /-- The indexing type for source affine opens over each target open. -/
  I : J → Type w
  /-- The source affine open cover over each target open. -/
  U : ∀ j, I j → X.Opens
  /-- The source opens cover the inverse image of the corresponding target open. -/
  iSup_eq_preimage : ∀ j, (⨆ i, U j i) = f ⁻¹ᵁ V j
  /-- Every source member is affine. -/
  affine_U : ∀ j i, IsAffineOpen (U j i)
  /-- The induced ring map on every affine-open pair is flat. -/
  appLE_flat :
    ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j,
      (CommRingCat.Hom.hom (f.appLE (V j) (U j i) e)).Flat

/-- A scheme morphism is flat exactly when every compatible affine-open pair induces a flat
map of section rings. -/
@[stacks 01U5]
theorem flat_iff_affineOpen_appLE_flat
    (f : X ⟶ S) :
    Flat f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).Flat := sorry

/-- A flat scheme morphism has the flat open cover consisting of the top opens on the source
and target. -/
def FlatOpenCover.singleton
    (f : X ⟶ S) (hflat : Flat f) : FlatOpenCover.{u, v, w} f where
  J := PUnit
  V := fun _ ↦ ⊤
  iSup_eq_top := by simp
  I := fun _ ↦ PUnit
  U := fun _ _ ↦ ⊤
  iSup_eq_preimage := by simp
  flat_resLE := by
    intro j i
    let e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens) := by simp
    exact ⟨e, AlgebraicGeometry.IsZariskiLocalAtSource.resLE
      (P := @AlgebraicGeometry.Flat) e hflat⟩

/-- Every member of a flat affine open cover gives a flat restriction over the corresponding
target open. -/
theorem FlatAffineOpenCover.flat_resLE
    (f : X ⟶ S) (𝒞 : FlatAffineOpenCover.{u, v, w} f) (j : 𝒞.J) (i : 𝒞.I j) :
    ∃ e : 𝒞.U j i ≤ f ⁻¹ᵁ 𝒞.V j,
      Flat (f.resLE (𝒞.V j) (𝒞.U j i) e) := sorry

/-- Forgetting affineness and sectionwise witnesses turns a flat affine open cover into a flat
open cover with the same chosen opens. -/
def FlatAffineOpenCover.toFlatOpenCover
    (f : X ⟶ S) (𝒞 : FlatAffineOpenCover.{u, v, w} f) : FlatOpenCover.{u, v, w} f where
  J := 𝒞.J
  V := 𝒞.V
  iSup_eq_top := 𝒞.iSup_eq_top
  I := 𝒞.I
  U := 𝒞.U
  iSup_eq_preimage := 𝒞.iSup_eq_preimage
  flat_resLE := 𝒞.flat_resLE f

/-- Flatness of a scheme morphism is local on compatible open covers. -/
@[stacks 01U5]
theorem flat_iff_hasFlatOpenCover
    (f : X ⟶ S) :
    Flat f ↔ Nonempty (FlatOpenCover f) := sorry

/-- Flatness of a scheme morphism is detected on compatible affine open covers. -/
@[stacks 01U5]
theorem flat_iff_hasFlatAffineOpenCover
    (f : X ⟶ S) :
    Flat f ↔ Nonempty (FlatAffineOpenCover f) := sorry

end AlgebraicGeometry.Scheme.Hom
