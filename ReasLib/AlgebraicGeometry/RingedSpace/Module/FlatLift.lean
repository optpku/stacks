/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Thickening.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension

/-!
# Flat lifts of modules along first-order thickenings

Flat lifts are modules flat over the thickened base, equipped with a specified
isomorphism from their reduction. Compatible isomorphisms define their classes,
and the ideal action gives their associated infinitesimal extensions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] (F : X.Modules)

/-- The identity infinitesimal comparison `c = 1`, as the pushforward-level map
`ℐ ⊗ i_* F ⟶ i_* (ℐ ⊗ F)` whose restriction is `𝟙 (ℐ ⊗ F)`. -/
def infMapId : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj (idealModule i ⊗ F) :=
  (pullbackPushforwardAdjunction i).homEquiv
    (kernelIdealSheaf i ⊗ (i _*).obj F) (idealModule i ⊗ F)
    ((Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) ((i _*).obj F)).inv ≫
      tensorHom (𝟙 (idealModule i))
        (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom)

/-- Restricting `infMapId` recovers `𝟙 (ℐ ⊗ F)`. -/
theorem infMapId_restrict :
    infinitesimalMap_restrict i (infMapId i F) = 𝟙 (idealModule i ⊗ F) :=
  sorry

end AlgebraicGeometry.RingedSpace.Modules

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

/-- A pair `(F', α)` consisting of an `𝒪_{X'}`-module `F'` flat over `S'` and an
isomorphism `α : i^* F' ≅ F`. -/
structure FlatLift {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
    [IsFirstOrderThickening U.hom] (g : T ⟶ U) (F : T.left.Modules) where
  /-- The lifted `𝒪_{X'}`-module `F'`. -/
  module : T.right.Modules
  /-- Inverse image along `i` recovers `F`. -/
  restrictIso : (T.hom^*).obj module ≅ F
  /-- The lift is flat over `S'`. -/
  isFlatOver : SheafOfModules.IsFlatOver module g.right

namespace FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]

/-- Assemble a flat lift from an `𝒪_{X'}`-module, an isomorphism `i^* F' ≅ F`, and
relative flatness over `S'`. -/
def of (g : T ⟶ U) (F : T.left.Modules) (F' : T.right.Modules)
    (α : (T.hom^*).obj F' ≅ F) (hflat : SheafOfModules.IsFlatOver F' g.right) :
    FlatLift g F where
  module := F'
  restrictIso := α
  isFlatOver := hflat

/-- A flat lift is an `𝒪_{X'}`-module flat over `S'` together with an isomorphism
`i^* F' ≅ F`. -/
theorem spec {g : T ⟶ U} {F : T.left.Modules} (L : FlatLift g F) :
    Nonempty ((T.hom^*).obj L.module ≅ F) ∧ SheafOfModules.IsFlatOver L.module g.right :=
  ⟨⟨L.restrictIso⟩, L.isFlatOver⟩

/-- Morphisms of flat lifts, as maps of middle `𝒪_{X'}`-modules compatible with the
restriction isomorphisms. -/
structure Hom {g : T ⟶ U} {F : T.left.Modules} (L₁ L₂ : FlatLift g F) where
  /-- The underlying morphism of middle `𝒪_{X'}`-modules. -/
  hom : L₁.module ⟶ L₂.module
  /-- Inverse image along `i` intertwines the restriction isomorphisms. -/
  restrictIso_hom :
    (T.hom^*).map hom ≫ L₂.restrictIso.hom = L₁.restrictIso.hom

namespace Hom

variable {g : T ⟶ U} {F : T.left.Modules}

/-- Assemble a morphism of flat lifts from a middle map compatible with the restriction
isomorphisms. -/
def of {L₁ L₂ : FlatLift g F} (hom : L₁.module ⟶ L₂.module)
    (restrictIso_hom :
      (T.hom^*).map hom ≫ L₂.restrictIso.hom = L₁.restrictIso.hom) :
    Hom L₁ L₂ where
  hom := hom
  restrictIso_hom := restrictIso_hom

/-- A morphism of flat lifts intertwines the restriction isomorphisms. -/
theorem spec {L₁ L₂ : FlatLift g F} (φ : Hom L₁ L₂) :
    (T.hom^*).map φ.hom ≫ L₂.restrictIso.hom = L₁.restrictIso.hom :=
  φ.restrictIso_hom

/-- Identity morphisms of flat lifts. -/
def id (L : FlatLift g F) : Hom L L where
  hom := 𝟙 L.module
  restrictIso_hom :=
    (congrArg (fun k => k ≫ L.restrictIso.hom) ((T.hom^*).map_id L.module)).trans
      (Category.id_comp L.restrictIso.hom)

/-- Composition of morphisms of flat lifts. -/
def comp {L₁ L₂ L₃ : FlatLift g F} (φ : Hom L₁ L₂) (ψ : Hom L₂ L₃) : Hom L₁ L₃ where
  hom := φ.hom ≫ ψ.hom
  restrictIso_hom := by
    calc
      (T.hom^*).map (φ.hom ≫ ψ.hom) ≫ L₃.restrictIso.hom =
          ((T.hom^*).map φ.hom ≫ (T.hom^*).map ψ.hom) ≫ L₃.restrictIso.hom :=
        congrArg (fun k => k ≫ L₃.restrictIso.hom) ((T.hom^*).map_comp φ.hom ψ.hom)
      _ = (T.hom^*).map φ.hom ≫ ((T.hom^*).map ψ.hom ≫ L₃.restrictIso.hom) :=
        Category.assoc _ _ _
      _ = (T.hom^*).map φ.hom ≫ L₂.restrictIso.hom :=
        congrArg (fun k => (T.hom^*).map φ.hom ≫ k) ψ.restrictIso_hom
      _ = L₁.restrictIso.hom := φ.restrictIso_hom

end Hom

variable {g : T ⟶ U} {F : T.left.Modules}

/-- The extension with identity infinitesimal comparison associated to a flat lift
`(F', α)`, using the adjunct of `α` as projection and the kernel-ideal action of `F'`
compared along `α⁻¹` as inclusion. -/
def toInfinitesimalExtension (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    (L : FlatLift g F) :
    InfinitesimalExtension T.hom F (idealModule T.hom ⊗ F) (infMapId T.hom F) := by
  let ι :=
    (T.hom _*).map
        (tensorHom (𝟙 (idealModule T.hom)) L.restrictIso.inv ≫
          actionToIdealMulRestrict T.hom L.module) ≫
      (ModuleExtension.ofPullback T.hom L.module).ι
  let π := (pullbackPushforwardAdjunction T.hom).homEquiv L.module F L.restrictIso.hom
  have certificate : ∃ (w : ι ≫ π = 0)
      (hSE : (ShortComplex.mk ι π w).ShortExact),
      infinitesimalMap T.hom ι π w hSE = infMapId T.hom F := by
    sorry
  have w : ι ≫ π = 0 := by
    obtain ⟨w, _⟩ := certificate
    exact w
  have hSE : (ShortComplex.mk ι π w).ShortExact := by
    obtain ⟨_, hSE, _⟩ := certificate
    exact hSE
  have hc : infinitesimalMap T.hom ι π w hSE = infMapId T.hom F := by
    obtain ⟨_, _, hc⟩ := certificate
    exact hc
  exact { module := L.module, ι := ι, π := π, w := w, shortExact := hSE, infMap_eq := hc }

/-- The middle `𝒪_{X'}`-module of the associated infinitesimal extension is the lifted module. -/
theorem toInfinitesimalExtension_module (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] (L : FlatLift g F) :
    (toInfinitesimalExtension hg L).module = L.module :=
  rfl

/-- The projection of the associated infinitesimal extension is the adjunct of `α`. -/
theorem toInfinitesimalExtension_π (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] (L : FlatLift g F) :
    (toInfinitesimalExtension hg L).π =
      (pullbackPushforwardAdjunction T.hom).homEquiv L.module F L.restrictIso.hom :=
  rfl

/-- The inclusion of the associated infinitesimal extension is the pushforward of the kernel-ideal
action compared along `α⁻¹`, followed by the canonical inclusion of `ℐ F'`. -/
theorem toInfinitesimalExtension_ι (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] (L : FlatLift g F) :
    (toInfinitesimalExtension hg L).ι =
      (T.hom _*).map
          (tensorHom (𝟙 (idealModule T.hom)) L.restrictIso.inv ≫
            actionToIdealMulRestrict T.hom L.module) ≫
        (ModuleExtension.ofPullback T.hom L.module).ι :=
  rfl

/-- Two flat lifts are isomorphic when a middle-module isomorphism intertwines their
specified restriction isomorphisms. -/
def Isomorphic (L M : FlatLift g F) : Prop :=
  ∃ e : L.module ≅ M.module,
    (T.hom^*).map e.hom ≫ M.restrictIso.hom = L.restrictIso.hom

/-- Compatible isomorphisms define an equivalence relation on flat lifts. -/
def isoSetoid (g : T ⟶ U) (F : T.left.Modules) : Setoid (FlatLift g F) where
  r := Isomorphic
  iseqv := {
    refl := fun L => ⟨Iso.refl L.module,
      (congrArg (fun k => k ≫ L.restrictIso.hom) ((T.hom^*).map_id L.module)).trans
        (Category.id_comp L.restrictIso.hom)⟩
    symm := by
      rintro L M ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      change (T.hom^*).map e.inv ≫ L.restrictIso.hom = M.restrictIso.hom
      calc
        (T.hom^*).map e.inv ≫ L.restrictIso.hom =
            (T.hom^*).map e.inv ≫ ((T.hom^*).map e.hom ≫ M.restrictIso.hom) := by
          exact congrArg (fun k => (T.hom^*).map e.inv ≫ k) he.symm
        _ = ((T.hom^*).map e.inv ≫ (T.hom^*).map e.hom) ≫ M.restrictIso.hom :=
          (Category.assoc _ _ _).symm
        _ = (T.hom^*).map (e.inv ≫ e.hom) ≫ M.restrictIso.hom :=
          congrArg (fun k => k ≫ M.restrictIso.hom) ((T.hom^*).map_comp e.inv e.hom).symm
        _ = (T.hom^*).map (𝟙 M.module) ≫ M.restrictIso.hom :=
          congrArg (fun k => (T.hom^*).map k ≫ M.restrictIso.hom) e.inv_hom_id
        _ = 𝟙 ((T.hom^*).obj M.module) ≫ M.restrictIso.hom :=
          congrArg (fun k => k ≫ M.restrictIso.hom) ((T.hom^*).map_id M.module)
        _ = M.restrictIso.hom := Category.id_comp _
    trans := by
      rintro L M N ⟨e, he⟩ ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      change (T.hom^*).map (e.hom ≫ f.hom) ≫ N.restrictIso.hom = L.restrictIso.hom
      calc
        (T.hom^*).map (e.hom ≫ f.hom) ≫ N.restrictIso.hom =
            ((T.hom^*).map e.hom ≫ (T.hom^*).map f.hom) ≫ N.restrictIso.hom :=
          congrArg (fun k => k ≫ N.restrictIso.hom) ((T.hom^*).map_comp e.hom f.hom)
        _ = (T.hom^*).map e.hom ≫ ((T.hom^*).map f.hom ≫ N.restrictIso.hom) :=
          Category.assoc _ _ _
        _ = (T.hom^*).map e.hom ≫ M.restrictIso.hom :=
          congrArg (fun k => (T.hom^*).map e.hom ≫ k) hf
        _ = L.restrictIso.hom := he }

/-- Isomorphism classes of flat lifts with their specified reduction isomorphisms. -/
abbrev IsomorphismClass (g : T ⟶ U) (F : T.left.Modules) := Quotient (isoSetoid g F)

namespace IsomorphismClass

/-- The isomorphism class represented by a flat lift. -/
def mk (L : FlatLift g F) : IsomorphismClass g F := Quotient.mk (isoSetoid g F) L

end IsomorphismClass

end FlatLift

end AlgebraicGeometry.RingedSpace.Thickening.Hom
