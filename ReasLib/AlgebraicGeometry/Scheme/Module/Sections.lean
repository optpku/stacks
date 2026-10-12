/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Subobject
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Global sections of scheme modules

This leaf specializes the additive section-object interface to schemes and
adds the pullback map supplied by the pullback–pushforward adjunction.
-/

@[expose] public section

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The section submodule on an affine open cut out by a subobject of a scheme module. -/
@[stacks 01YL "submodule of affine-open sections associated to a subobject",
  stacks 0AXT "affine-open sections of a submodule"]
abbrev subobjectSectionsSubmoduleOnAffineOpen
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : X.affineOpens) :
    Submodule Γ(X, U.1) (ℱ.val.obj (op U.1)) :=
  RingedSpace.Modules.subobjectSectionsSubmodule 𝒢 U.1

/-- The additive group of global sections of a scheme module. -/
abbrev globalSections (F : X.Modules) : AddCommGrpCat :=
  RingedSpace.moduleGlobalSections F

/-- The map on global sections induced by a morphism of scheme modules. -/
abbrev globalSectionsMap {F G : X.Modules} (φ : F ⟶ G) :
    globalSections F ⟶ globalSections G :=
  RingedSpace.moduleGlobalSectionsMap φ

/-- Global sections of a scheme module with scalars restricted along an explicit
ring map `R →+* Γ(X, ⊤)`. -/
@[stacks 01BH "scheme global-section scalars along an explicit map"]
noncomputable abbrev globalSectionsModuleAlong
    (R : Type u) [CommRing R] (X : Scheme.{u})
    (α : R →+* Γ(X, ⊤)) (F : X.Modules) : Module R Γ(F, ⊤) :=
  Module.compHom Γ(F, ⊤) α

/-- The pullback map on global sections induced by the unit
`F ⟶ f_* f^* F` of the canonical scheme-module adjunction. -/
@[stacks 01BH "pullback on module global sections"]
abbrev globalSectionsPullback (f : X ⟶ Y) (F : Y.Modules) :
    globalSections F ⟶ globalSections ((pullback f).obj F) :=
  Hom.app ((pullbackPushforwardAdjunction f).unit.app F) ⊤

/-- Pullback of a compatible global section along a scheme morphism. This is the section-level
form of `globalSectionsPullback`, reconstructed from its value on the top open. -/
@[stacks 01BH "pullback of a compatible module section"]
noncomputable def sectionsPullback (f : X ⟶ Y) (F : Y.Modules) :
    F.sections → ((pullback f).obj F).sections :=
  fun s ↦ RingedSpace.sectionFromTop ((pullback f).obj F)
    ((globalSectionsPullback f F).hom (s.1 (Opposite.op ⊤)))

/-- Evaluating a pulled-back compatible section is restriction of its pulled-back top value. -/
@[simp, stacks 01BH "pulled-back section evaluation"]
theorem sectionsPullback_apply
    (f : X ⟶ Y) (F : Y.Modules) (s : F.sections) (U : (X.Opens)ᵒᵖ) :
    (sectionsPullback f F s).1 U =
      ((pullback f).obj F).val.map (RingedSpace.topOpenRestriction U)
        ((globalSectionsPullback f F).hom (s.1 (Opposite.op ⊤))) := sorry

/-- Evaluation at the top open recovers the pullback map on top-open module values. -/
@[simp, stacks 01BH "pulled-back section top evaluation"]
theorem sectionsPullback_apply_top
    (f : X ⟶ Y) (F : Y.Modules) (s : F.sections) :
    (sectionsPullback f F s).1 (Opposite.op (⊤ : X.Opens)) =
      (globalSectionsPullback f F).hom (s.1 (Opposite.op ⊤)) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}

/-- The global-sections functor with scalars restricted along the map induced by
`f : X ⟶ Spec R`. This bundled functor is the primary module-valued owner. -/
@[stacks 01BH "scheme global-sections functor over an affine base"]
noncomputable abbrev globalSectionsFunctor
    (f : X ⟶ Spec (CommRingCat.of R)) : X.Modules ⥤ ModuleCat R :=
  RingedSpace.moduleGlobalSectionsRestrictionFunctor
    X.toRingedSpace (globalSectionsMap f)

/-- Global sections of `F`, bundled as an `R`-module through `f : X ⟶ Spec R`. -/
@[stacks 01BH "bundled scheme global sections over an affine base"]
noncomputable abbrev globalSectionsMod
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) : ModuleCat R :=
  (globalSectionsFunctor f).obj F

/-- The global sections of a scheme module, as an `R`-module induced by the explicit
map `globalSectionsMap f`. This is the unbundled compatibility view of
`globalSectionsMod f F`. -/
@[stacks 01BH "scheme global-section module along an affine map"]
noncomputable abbrev globalSectionsModule
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) :
    Module R Γ(F, ⊤) :=
  Scheme.Modules.globalSectionsModuleAlong R X (globalSectionsMap f) F

/-- The module structure on sections of `F` over `U`, induced by `f : X ⟶ Y` over an inclusion
`U ⊆ f⁻¹(V)` of open subsets. -/
@[stacks 01BH "scheme section module along a morphism"]
noncomputable abbrev sectionsModule
    (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    (F : X.Modules) : Module Γ(Y, V) Γ(F, U) :=
  Module.compHom Γ(F, U) (sectionsMapAlong f V U hU)

/-- Sections of `F` on `U`, bundled as a module over `Γ(Y, V)` through `f`. -/
@[stacks 01BH "bundled scheme section module along a morphism"]
noncomputable def sectionsMod
    (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    (F : X.Modules) : ModuleCat Γ(Y, V) :=
  @ModuleCat.of Γ(Y, V) _ Γ(F, U) _ (sectionsModule f V U hU F)

/-- The bundled section module is independent of the proof of the open containment. -/
@[stacks 01BH "bundled section module proof independence"]
theorem sectionsMod_proof_irrel
    (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens) (hU hU' : U ≤ f ⁻¹ᵁ V)
    (F : X.Modules) :
    sectionsMod f V U hU F = sectionsMod f V U hU' F := sorry

/-- Sections of `F` on `U`, bundled as an `R`-module through `f : X ⟶ Spec R`. -/
@[stacks 01BH "bundled scheme section module over an affine base"]
noncomputable def sectionsModOverSpec
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens)
    (F : X.Modules) : ModuleCat R :=
  @ModuleCat.of R _ Γ(F, U) _
    (Module.compHom Γ(F, U) (sectionsMap f U))

/-- The scalar actions on `Γ(F, U)` induced by `Γ(Y, V) → Γ(X, U)` form a scalar tower. -/
@[stacks 01BH "scheme section scalar tower"]
theorem sectionsModule_isScalarTower
    (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    (F : X.Modules) :
    @IsScalarTower Γ(Y, V) Γ(X, U) Γ(F, U)
      (sectionsAlgebra f V U hU).toSMul
      (inferInstance : SMul Γ(X, U) Γ(F, U))
      (sectionsModule f V U hU F).toSMul := sorry

end AlgebraicGeometry.Scheme.Hom
