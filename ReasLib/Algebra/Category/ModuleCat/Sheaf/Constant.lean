module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheaves over a constant ring sheaf

A `ModuleCat R`-valued sheaf has a canonical view as a sheaf of modules over
the constant ring sheaf `R̲`.  This file packages that construction as functors
on presheaves and sheaves, so downstream finiteness and exactness APIs can use
the canonical `SheafOfModules` owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type w} [Ring R]

namespace ConstantModule

/-- The canonical map from the constant ring presheaf with value `R` to the
constant ring sheaf. -/
abbrev ringMap
    [HasWeakSheafify J RingCat.{w}] :
    (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶
      ((constantSheaf J RingCat.{w}).obj (RingCat.of R)).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))

/-- The constant-ring sheafification map is locally injective. -/
noncomputable instance ringMap_isLocallyInjective
    [HasWeakSheafify J RingCat.{w}]
    [J.WEqualsLocallyBijective RingCat.{w}] :
    Presheaf.IsLocallyInjective J (ringMap (J := J) (R := R)) := sorry

/-- The constant-ring sheafification map is locally surjective. -/
noncomputable instance ringMap_isLocallySurjective
    [HasWeakSheafify J RingCat.{w}]
    [J.WEqualsLocallyBijective RingCat.{w}] :
    Presheaf.IsLocallySurjective J (ringMap (J := J) (R := R)) := sorry

/-- The canonical `R`-module structure on a section of a `ModuleCat R`-valued
sheaf, displayed over the constant ring presheaf. -/
abbrev sectionModule (F : Sheaf J (ModuleCat.{w} R)) (X : Cᵒᵖ) :
    Module (((Functor.const Cᵒᵖ).obj (RingCat.of R)).obj X)
      ((F.obj ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj X) :=
  inferInstanceAs (Module R (F.obj.obj X))

/-- The canonical section module is available to typeclass search when a
`ModuleCat R`-valued sheaf is viewed over the constant ring presheaf. -/
instance sectionModule_instance
    (F : Sheaf J (ModuleCat.{w} R)) (X : Cᵒᵖ) :
    Module (((Functor.const Cᵒᵖ).obj (RingCat.of R)).obj X)
      ((F.obj ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj X) :=
  sectionModule F X

/-- Restriction maps of a `ModuleCat R`-valued sheaf are linear over the
constant ring presheaf. -/
theorem restriction_map_smul
    (F : Sheaf J (ModuleCat.{w} R)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (r : R) (m : F.obj.obj X) :
    (F.obj.map f).hom (r • m) =
      (RingHom.id R) r • (F.obj.map f).hom m := sorry

/-- The underlying presheaf of `R`-modules of a `ModuleCat R`-valued sheaf,
regarded as a module over the constant ring presheaf. -/
abbrev presheaf (F : Sheaf J (ModuleCat.{w} R)) :
    PresheafOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of R)) :=
  PresheafOfModules.ofPresheaf
    (F.obj ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})
    (fun {_ _} f r m ↦ restriction_map_smul F f r m)

/-- A morphism of `ModuleCat R`-valued sheaves induces the corresponding
morphism between their constant-ring module presheaves. -/
def presheafMap
    {F G : Sheaf J (ModuleCat.{w} R)} (η : F ⟶ G) :
    presheaf F ⟶ presheaf G where
  app U := η.hom.app U
  naturality := sorry

/-- The presheaf map induced by an identity morphism is the identity map. -/
theorem presheafMap_id (F : Sheaf J (ModuleCat.{w} R)) :
    presheafMap (𝟙 F) = 𝟙 (presheaf F) := sorry

/-- The presheaf map induced by a composite is the composite of the induced maps. -/
theorem presheafMap_comp
    {F G H : Sheaf J (ModuleCat.{w} R)} (η : F ⟶ G) (θ : G ⟶ H) :
    presheafMap (η ≫ θ) = presheafMap η ≫ presheafMap θ := sorry

/-- Viewing a `ModuleCat R`-valued sheaf as a module presheaf over the
constant ring presheaf is functorial. -/
def presheafFunctor :
    Sheaf J (ModuleCat.{w} R) ⥤
      PresheafOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of R)) where
  obj F := presheaf F
  map η := presheafMap η
  map_id := presheafMap_id
  map_comp := presheafMap_comp

end ConstantModule

variable [HasWeakSheafify J RingCat.{w}]
variable [J.WEqualsLocallyBijective RingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The canonical view of a `ModuleCat R`-valued sheaf as a sheaf of modules
over the constant ring sheaf `R̲`. -/
@[stacks 093N "constant-module view"]
noncomputable abbrev toConstantModuleSheaf (F : Sheaf J (ModuleCat.{w} R)) :
    SheafOfModules ((constantSheaf J RingCat.{w}).obj (RingCat.of R)) :=
  (PresheafOfModules.sheafification
    (ConstantModule.ringMap (J := J) (R := R))).obj
      (ConstantModule.presheaf F)

namespace ConstantModule

/-- A morphism of `ModuleCat R`-valued sheaves induces a morphism between
their canonical constant-ring module-sheaf views. -/
noncomputable def sheafMap
    {F G : Sheaf J (ModuleCat.{w} R)} (η : F ⟶ G) :
    F.toConstantModuleSheaf ⟶ G.toConstantModuleSheaf :=
  (PresheafOfModules.sheafification
    (ringMap (J := J) (R := R))).map (presheafMap η)

/-- The sheaf map induced by an identity morphism is the identity map. -/
theorem sheafMap_id (F : Sheaf J (ModuleCat.{w} R)) :
    sheafMap (𝟙 F) = 𝟙 F.toConstantModuleSheaf := sorry

/-- The sheaf map induced by a composite is the composite of the induced maps. -/
theorem sheafMap_comp
    {F G H : Sheaf J (ModuleCat.{w} R)} (η : F ⟶ G) (θ : G ⟶ H) :
    sheafMap (η ≫ θ) = sheafMap η ≫ sheafMap θ := sorry

/-- The canonical constant-ring module-sheaf view is functorial. -/
noncomputable def sheafFunctor :
    Sheaf J (ModuleCat.{w} R) ⥤
      SheafOfModules ((constantSheaf J RingCat.{w}).obj (RingCat.of R)) where
  obj F := F.toConstantModuleSheaf
  map η := sheafMap η
  map_id := sheafMap_id
  map_comp := sheafMap_comp

end ConstantModule

end CategoryTheory.Sheaf
