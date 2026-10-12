/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Open-cover criteria for flat scheme modules

This leaf records the sectionwise and open-local forms of relative flatness of
quasi-coherent scheme modules.  The cover structures retain their chosen opens,
so they can be constructed once and then reused by localization arguments.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- The `f⁻¹𝒪_S`-module obtained from `ℱ : X.Modules` by restriction of scalars along `f`. -/
abbrev relativeModuleOver
    (ℱ : X.Modules) (f : X ⟶ S) :=
  SheafOfModules.relativeModule ℱ f.toShHom

/-- Flatness of sections of `ℱ` over a compatible affine-open pair `U ⊆ f⁻¹(V)`. -/
@[stacks 01U4 "flatness of sections on a compatible open pair"]
abbrev flatOnAffineOpenPair
    (ℱ : X.Modules) (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) : Prop :=
  Module.Flat Γ(S, V) (Scheme.Hom.sectionsMod f V U e ℱ)

/-- Sectionwise flatness of `ℱ` over every compatible affine-open pair over `S`. -/
@[stacks 01U4 "affine-open sectionwise flatness"]
abbrev affineOpenSectionsFlatOver
    (ℱ : X.Modules) (f : X ⟶ S) : Prop :=
  ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
    ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
      flatOnAffineOpenPair ℱ f U V e

/-- Open-cover data witnessing flatness of a module over a scheme morphism. -/
structure FlatOpenCover
    (ℱ : X.Modules) (f : X ⟶ S) where
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
  /-- The restricted module is flat over every restricted base scheme. -/
  flat_restrict :
    ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, flatOver (ℱ.restrict (U j i).ι) (f.resLE (V j) (U j i) e)

/-- Affine-open-cover data witnessing flatness of a module over a scheme morphism. -/
structure FlatAffineOpenCover
    (ℱ : X.Modules) (f : X ⟶ S) where
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
  /-- Sections on every affine-open pair are flat over the target section ring. -/
  appLE_flat :
    ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, flatOnAffineOpenPair ℱ f (U j i) (V j) e

/-- A quasi-coherent module is flat over a scheme morphism if and only if its sections over
every compatible pair of affine opens are flat over the target section ring. -/
@[stacks 01U4]
theorem flatOver_iff_affineOpenSectionsFlatOver
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S) :
    flatOver ℱ f ↔ affineOpenSectionsFlatOver ℱ f := sorry

/-- Restricting a relatively flat quasi-coherent module to compatible source and target opens
preserves relative flatness. -/
@[stacks 01U4]
theorem flatOver_resLE_of_flatOver
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] {f : X ⟶ S}
    (hflat : flatOver ℱ f)
    {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    flatOver (ℱ.restrict U.ι) (f.resLE V U e) := sorry

/-- A relatively flat quasi-coherent module has the flat open cover consisting of the top
opens on the source and target. -/
def FlatOpenCover.singleton
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S) (hflat : flatOver ℱ f) :
    FlatOpenCover.{u, v, w} ℱ f where
  J := PUnit
  V := fun _ ↦ ⊤
  iSup_eq_top := by simp
  I := fun _ ↦ PUnit
  U := fun _ _ ↦ ⊤
  iSup_eq_preimage := by simp
  flat_restrict := by
    intro j i
    let e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens) := by simp
    exact ⟨e, flatOver_resLE_of_flatOver ℱ hflat e⟩

/-- Every member of a flat affine open cover gives a relatively flat restriction over the
corresponding target open. -/
theorem FlatAffineOpenCover.flatOver_restrict
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S)
    (𝒞 : FlatAffineOpenCover.{u, v, w} ℱ f) (j : 𝒞.J) (i : 𝒞.I j) :
    ∃ e : 𝒞.U j i ≤ f ⁻¹ᵁ 𝒞.V j,
      flatOver (ℱ.restrict (𝒞.U j i).ι) (f.resLE (𝒞.V j) (𝒞.U j i) e) := sorry

/-- Forgetting affineness and sectionwise witnesses turns a flat affine open cover into a flat
open cover with the same chosen opens. -/
def FlatAffineOpenCover.toFlatOpenCover
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S)
    (𝒞 : FlatAffineOpenCover.{u, v, w} ℱ f) : FlatOpenCover.{u, v, w} ℱ f where
  J := 𝒞.J
  V := 𝒞.V
  iSup_eq_top := 𝒞.iSup_eq_top
  I := 𝒞.I
  U := 𝒞.U
  iSup_eq_preimage := 𝒞.iSup_eq_preimage
  flat_restrict := 𝒞.flatOver_restrict ℱ f

/-- A quasi-coherent module is flat over a scheme morphism if and only if it admits compatible
open-cover data on which all restrictions are relatively flat. -/
@[stacks 01U4]
theorem flatOver_iff_hasFlatOpenCover
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S) :
    flatOver ℱ f ↔ Nonempty (FlatOpenCover ℱ f) := sorry

/-- A quasi-coherent module is flat over a scheme morphism if and only if it admits compatible
affine open covers whose section modules are flat over the target section rings. -/
@[stacks 01U4]
theorem flatOver_iff_hasFlatAffineOpenCover
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S) :
    flatOver ℱ f ↔ Nonempty (FlatAffineOpenCover ℱ f) := sorry

end AlgebraicGeometry.Scheme.Modules
