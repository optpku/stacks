/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_11_2_Canonical
public import stacks_project.Chap91.Remark_91_10_7_Extension
public import stacks_project.Chap91.Remark_91_10_10_Thickening

/-!
# Flat lifts of modules along a first-order thickening of ringed topoi

A flat lift of an `O`-module `F` along `π : O' ⟶ O` is a pair `(F', α)` with `F'` an
`O'`-module flat over `O_{B'}` and `α : i^* F' ⟶ F` an isomorphism. Each such pair
determines an 08MB mixed-scalar extension with infinitesimal map `c = 𝟙`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {OB' O' O : Sheaf J CommRingCat.{max u v}}

/-- A pair `(F', α)` consisting of an `O'`-module `F'` flat over `O_{B'}` and an
isomorphism `α : i^* F' ⟶ F`. -/
structure FlatLift (π : O' ⟶ O) [IsFirstOrderThickening π]
    [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
    (f' : OB' ⟶ O') (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O) where
  /-- The lifted `O'`-module `F'`. -/
  module : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'
  /-- The comparison morphism `i^* F' ⟶ F`. -/
  isoHom : (extendScalars (ringSheafMap π)).obj module ⟶ F
  /-- The comparison morphism is an isomorphism. -/
  isoHom_isIso : IsIso isoHom
  /-- The lift is flat over `O_{B'}`. -/
  isFlatOver : IsFlat OB' ((restrictionAlong f').obj module)

namespace FlatLift

variable (π : O' ⟶ O) [hπ : IsFirstOrderThickening π]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f' : OB' ⟶ O')
variable (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)

/-- Assemble a flat lift from an `O'`-module, an isomorphism `i^* F' ≅ F`, and relative
flatness over `O_{B'}`. -/
def of (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
    (iso : (extendScalars (ringSheafMap π)).obj F' ≅ F)
    (hflat : IsFlat OB' ((restrictionAlong f').obj F')) : FlatLift π f' F where
  module := F'
  isoHom := iso.hom
  isoHom_isIso := Iso.isIso_hom iso
  isFlatOver := hflat

/-- A flat lift is an `O'`-module flat over `O_{B'}` together with an isomorphism
`i^* F' ⟶ F`. -/
theorem spec (L : FlatLift π f' F) :
    IsIso L.isoHom ∧ IsFlat OB' ((restrictionAlong f').obj L.module) := sorry

variable {π f' F}

/-- The infinitesimal comparison `I ⊗_O F ⟶ I F'` obtained by transporting
`idealMulInfMap` along `α⁻¹`. -/
def transportedInfMap (L : FlatLift π f' F) :
    moduleTensor (ideal π) F ⟶ idealMul π L.module :=
  moduleTensorMap (𝟙 (ideal π)) (@inv _ _ _ _ L.isoHom L.isoHom_isIso) ≫
    idealMulInfMap π L.module

/-- `transportedInfMap` is `idealMulInfMap` after tensoring with `α⁻¹`. -/
theorem transportedInfMap_eq (L : FlatLift π f' F) :
    transportedInfMap L =
      moduleTensorMap (𝟙 (ideal π)) (@inv _ _ _ _ L.isoHom L.isoHom_isIso) ≫
        idealMulInfMap π L.module := sorry

/-- Morphisms of flat lifts, as isomorphisms of middle `O'`-modules compatible with the
comparison morphisms. -/
structure Hom (L₁ L₂ : FlatLift π f' F) where
  /-- The underlying morphism of middle `O'`-modules. -/
  hom : L₁.module ⟶ L₂.module
  /-- Inverse image along `i` intertwines the comparison morphisms. -/
  comm : L₁.isoHom = (extendScalars (ringSheafMap π)).map hom ≫ L₂.isoHom
  /-- The underlying morphism is an isomorphism. -/
  isIso : IsIso hom

namespace Hom

/-- Assemble a morphism of flat lifts from an isomorphism of middle modules compatible
with the comparison morphisms. -/
def of {L₁ L₂ : FlatLift π f' F} (hom : L₁.module ⟶ L₂.module)
    (comm : L₁.isoHom = (extendScalars (ringSheafMap π)).map hom ≫ L₂.isoHom)
    (isIso : IsIso hom) : Hom L₁ L₂ where
  hom := hom
  comm := comm
  isIso := isIso

/-- A morphism of flat lifts intertwines the comparison morphisms and is an
isomorphism on middle modules. -/
theorem spec {L₁ L₂ : FlatLift π f' F} (φ : Hom L₁ L₂) :
    L₁.isoHom = (extendScalars (ringSheafMap π)).map φ.hom ≫ L₂.isoHom ∧
      IsIso φ.hom := sorry

end Hom

variable {OB : Sheaf J CommRingCat.{max u v}} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening τ]
variable {f : OB ⟶ O} [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f') {hcomm : f' ≫ π = τ ≫ f}

/-- The 08MB extension with infinitesimal map `c = 𝟙` associated to a flat lift
`(F', α)`. Short exactness of `0 ⟶ I ⊗_O F ⟶ F' ⟶ F ⟶ 0` uses that `(f, f')` is
strict and that `F` is flat over `O_B`, so that `idealMulInfMap` is invertible by
Lemma 91.11.2. -/
def toModuleExtension [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (L : FlatLift π f' F) :
    ModuleExtension hπ.isSquareZero F (moduleTensor (ideal π) F)
      (𝟙 (moduleTensor (ideal π) F)) where
  module := L.module
  incl := (restrictionAlong π).map (transportedInfMap L) ≫ (ofPullback π L.module).ι
  proj := extendRestrictHomEquiv (ringSheafMap π) L.module F L.isoHom
  zero := sorry
  shortExact := sorry
  compatible := sorry

/-- The middle `O'`-module of the associated 08MB extension is the lifted module. -/
theorem toModuleExtension_module [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (L : FlatLift π f' F) :
    (toModuleExtension f' hstrict L).module = L.module := sorry

/-- The projection of the associated 08MB extension is the adjunct of `α`. -/
theorem toModuleExtension_proj [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (L : FlatLift π f' F) :
    (toModuleExtension f' hstrict L).proj =
      extendRestrictHomEquiv (ringSheafMap π) L.module F L.isoHom := sorry

/-- Rebuild a flat lift from an 08MB extension with infinitesimal map `c = 𝟙`.
Relative flatness of the middle module over `O_{B'}` uses Lemma 91.11.2, so this
requires a strict square, flatness of `F` over `O_B`, and existence of at least
one flat lift (equivalently, invertibility of `f^* J ⊗_O F ⟶ I ⊗_O F`). -/
def ofModuleExtension [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (h_exists : Nonempty (FlatLift π f' F))
    (E : ModuleExtension hπ.isSquareZero F (moduleTensor (ideal π) F)
      (𝟙 (moduleTensor (ideal π) F))) :
    FlatLift π f' F where
  module := E.module
  isoHom := (extendRestrictHomEquiv (ringSheafMap π) E.module F).symm E.proj
  isoHom_isIso := sorry
  isFlatOver := sorry

/-- The middle `O'`-module of the rebuilt lift is the middle term of the extension. -/
theorem ofModuleExtension_module [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (h_exists : Nonempty (FlatLift π f' F))
    (E : ModuleExtension hπ.isSquareZero F (moduleTensor (ideal π) F)
      (𝟙 (moduleTensor (ideal π) F))) :
    (ofModuleExtension f' hstrict h_exists E).module = E.module := sorry

/-- The comparison morphism of the rebuilt lift is the adjunct of the extension
projection. -/
theorem ofModuleExtension_isoHom [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (h_exists : Nonempty (FlatLift π f' F))
    (E : ModuleExtension hπ.isSquareZero F (moduleTensor (ideal π) F)
      (𝟙 (moduleTensor (ideal π) F))) :
    (ofModuleExtension f' hstrict h_exists E).isoHom =
      (extendRestrictHomEquiv (ringSheafMap π) E.module F).symm E.proj := sorry

end FlatLift

end SheafOfModules.RingedSite.FirstOrderThickening
