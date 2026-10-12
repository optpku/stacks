/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import stacks_project.Chap91.Lemma_91_5_1_IdealMul
public import stacks_project.Chap91.Lemma_91_5_2_Comparison
public import stacks_project.Chap91.Remark_91_4_7_Extension
public import stacks_project.Chap91.Situation_91_3_1_Comparison
public import stacks_project.Chap91.Situation_91_6_2_Diagram

/-!
# Flat lifts of modules along a morphism of first-order thickenings

A flat lift of an `𝒪_X`-module `F` along a morphism of first-order thickenings is a
pair `(F', α)` with `F'` an `𝒪_{X'}`-module flat over `S'` and `α : i^* F' ≅ F`. The
identity infinitesimal comparison `c = 1` is the pushforward-level map whose restriction
is `𝟙 (ℐ ⊗ F)`, and each such pair determines an 08L4 extension with this comparison.
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
  sorry

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
  sorry

/-- Identity morphisms of flat lifts. -/
def id (L : FlatLift g F) : Hom L L where
  hom := 𝟙 L.module
  restrictIso_hom := sorry

/-- Composition of morphisms of flat lifts. -/
def comp {L₁ L₂ L₃ : FlatLift g F} (φ : Hom L₁ L₂) (ψ : Hom L₂ L₃) : Hom L₁ L₃ where
  hom := φ.hom ≫ ψ.hom
  restrictIso_hom := sorry

end Hom

variable {g : T ⟶ U} {F : T.left.Modules}

/-- The 08L4 extension with infinitesimal map `c = 1` associated to a flat lift
`(F', α)`, using the adjunct of `α` as projection and the kernel-ideal action of `F'`
compared along `α⁻¹` as inclusion. -/
def toInfinitesimalExtension (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    (L : FlatLift g F) :
    InfinitesimalExtension T.hom F (idealModule T.hom ⊗ F) (infMapId T.hom F) where
  module := L.module
  ι :=
    (T.hom _*).map
        (tensorHom (𝟙 (idealModule T.hom)) L.restrictIso.inv ≫
          actionToIdealMulRestrict T.hom L.module) ≫
      (ModuleExtension.ofPullback T.hom L.module).ι
  π := (pullbackPushforwardAdjunction T.hom).homEquiv L.module F L.restrictIso.hom
  w := sorry
  shortExact := sorry
  infMap_eq := sorry

/-- The middle `𝒪_{X'}`-module of the associated 08L4 extension is the lifted module. -/
theorem toInfinitesimalExtension_module (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] (L : FlatLift g F) :
    (toInfinitesimalExtension hg L).module = L.module :=
  sorry

/-- The projection of the associated 08L4 extension is the adjunct of `α`. -/
theorem toInfinitesimalExtension_π (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] (L : FlatLift g F) :
    (toInfinitesimalExtension hg L).π =
      (pullbackPushforwardAdjunction T.hom).homEquiv L.module F L.restrictIso.hom :=
  sorry

/-- The inclusion of the associated 08L4 extension is the pushforward of the kernel-ideal
action compared along `α⁻¹`, followed by the canonical inclusion of `ℐ F'`. -/
theorem toInfinitesimalExtension_ι (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] (L : FlatLift g F) :
    (toInfinitesimalExtension hg L).ι =
      (T.hom _*).map
          (tensorHom (𝟙 (idealModule T.hom)) L.restrictIso.inv ≫
            actionToIdealMulRestrict T.hom L.module) ≫
        (ModuleExtension.ofPullback T.hom L.module).ι :=
  sorry

end FlatLift

end AlgebraicGeometry.RingedSpace.Thickening.Hom
