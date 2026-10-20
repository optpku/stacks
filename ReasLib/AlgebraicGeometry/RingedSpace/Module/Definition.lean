/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Module sheaves on ringed spaces

This file specializes the general sheaves-of-modules and stalk API to the structure sheaf of a
ringed space.  Ringed-space-level structure-sheaf maps belong to
`AlgebraicGeometry.RingedSpace.Basic`; this module owns the module-sheaf abbreviations, functors,
and stalk API. Categorical facts are reused from the general `SheafOfModules` API, with specialized
inference bridges registered when typeclass search does not unfold the ringed-space abbreviations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RingedSpace

/-- The category of sheaves of modules over the structure sheaf of a ringed space. -/
abbrev Modules (X : RingedSpace.{u}) :=
  SheafOfModules.{u} X.ringCatSheaf

/-- The category of presheaves of modules over the structure presheaf of a ringed space. -/
abbrev PresheafModules (X : RingedSpace.{u}) :=
  PresheafOfModules.{u} (ringCatSheaf X).obj

/-- Sheafification from module presheaves to module sheaves on a fixed ringed space. -/
noncomputable abbrev moduleSheafification (X : RingedSpace.{u}) :
    X.PresheafModules ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

section

variable {X : RingedSpace.{u}}

/- The `RingedSpace.Modules` abbreviation fixes the underlying ring sheaf through
`ringCatSheaf`.  Typeclass search does not unfold that alias far enough to find the generic
commutative-ring stalk action, so this is a defeq bridge rather than a second construction. -/
/-- The canonical action of the local ring `𝒪_{X,x}` on the additive stalk of an `X.Modules`
object.  This specialized instance forwards directly to
`TopCat.Sheaf.ringSheafOfCommStalkModule` across the `RingedSpace.Modules` abbreviation. -/
noncomputable instance moduleStalkModule (ℱ : X.Modules) (x : X) :
    Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x) :=
  TopCat.Sheaf.ringSheafOfCommStalkModule ℱ x

/- Notation for the canonical restriction morphism `SheafOfModules.Hom.over`. -/
scoped[ModuleRestriction] notation:max φ " |_ " U => SheafOfModules.Hom.over φ U

/-- The stalk of an `X.Modules` object at `x`, bundled as a module over the stalk of the
structure sheaf. -/
noncomputable abbrev stalkModuleCat (ℱ : X.Modules) (x : X) :
    ModuleCat (X.presheaf.stalk x) :=
  (SheafOfModules.stalkFunctorOfCommRing X.sheaf x).obj ℱ

/-- Taking the stalk at `x` defines a functor from sheaves of modules on `X` to modules over the
stalk ring `𝒪_{X,x}`. -/
noncomputable abbrev stalkModuleFunctor (x : X) :
    X.Modules ⥤ ModuleCat (X.presheaf.stalk x) :=
  SheafOfModules.stalkFunctorOfCommRing X.sheaf x

/-- The stalk functor on a ringed space preserves all small colimits whenever additive
sheafification is available. -/
@[stacks 01AH "stalks preserve colimits", instance]
theorem stalkModuleFunctor_preservesColimits
    (x : X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesColimits (stalkModuleFunctor x) := sorry

/-- The morphism of stalk modules induced by a morphism of sheaves of modules on a ringed
space. -/
noncomputable abbrev moduleStalkHom
    (x : X) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    stalkModuleCat ℱ x ⟶ stalkModuleCat 𝒢 x :=
  (stalkModuleFunctor x).map φ

/-- The underlying function of the morphism induced on stalk modules. -/
noncomputable abbrev moduleStalkMap
    (x : X) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    stalkModuleCat ℱ x → stalkModuleCat 𝒢 x :=
  ConcreteCategory.hom (moduleStalkHom x φ)

/-- The short complex of modules over `𝒪_{X,x}` obtained by taking the stalk at `x` of every
term and morphism of a short complex of `X.Modules`. -/
noncomputable abbrev moduleStalkShortComplex
    (S : ShortComplex X.Modules) (x : X) :
    ShortComplex (ModuleCat (X.presheaf.stalk x)) :=
  SheafOfModules.stalkShortComplexOfCommRing X.sheaf S x

/-- The ringed-space specialization of the canonical linear equivalence between the stalk of a
unit module sheaf and its coefficient-ring stalk. -/
noncomputable abbrev unitStalkLinearEquiv (x : X) :
    stalkModuleCat (SheafOfModules.unit X.ringCatSheaf) x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x :=
  SheafOfModules.unitStalkLinearEquiv X.sheaf x

/-- The ringed-space specialization of the canonical linear map from the stalk of a unit module
sheaf to its coefficient-ring stalk. -/
noncomputable abbrev unitStalkLinearMap (x : X) :
    stalkModuleCat (SheafOfModules.unit X.ringCatSheaf) x ⟶
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  SheafOfModules.unitStalkLinearMap X.sheaf x

/-- A morphism of module sheaves sends the germ of a section to the germ of its sectionwise
image. -/
theorem moduleStalkMap_germ
    (x : X) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢)
    (U : Opens X) (hx : x ∈ U) (m : ℱ.val.obj (Opposite.op U)) :
    moduleStalkMap x φ (TopCat.Presheaf.germ ℱ.val.presheaf U x hx m) =
      TopCat.Presheaf.germ 𝒢.val.presheaf U x hx (φ.val.app (Opposite.op U) m) := sorry

end

end RingedSpace

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- Direct image of module sheaves along a morphism of ringed spaces, obtained by restricting
scalars along its structure-sheaf morphism. -/
noncomputable abbrev pushforward :
    X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward (toRingCatSheafHom f)

/-- Inverse image of module sheaves along a morphism of ringed spaces. -/
noncomputable abbrev pullback :
    Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback (toRingCatSheafHom f)

/-- The canonical adjunction from pullback to pushforward of module sheaves
along a morphism of ringed spaces. -/
noncomputable abbrev pullbackPushforwardAdjunction :
    pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)

end RingedSpace.Hom

/- Notation for direct and inverse image of module sheaves on ringed spaces. -/
scoped notation:max f:max " _*" => RingedSpace.Hom.pushforward f
scoped notation:max f:max "^*" => RingedSpace.Hom.pullback f

end AlgebraicGeometry
