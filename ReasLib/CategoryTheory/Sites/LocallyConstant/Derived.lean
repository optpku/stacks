module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived restriction of locally constant sheaves

This leaf owns the canonical comparison between an ambient constant sheaf and its restriction to
a slice site, together with the module-category instances needed to pass to derived categories.
The chapter-facing statements only consume these owners.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v w w'

namespace CategoryTheory.Sheaf

section Constant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]
variable [HasWeakSheafify J D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]
variable {FD : D → D → Type*} {CD : D → Type*}
variable [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
variable [J.WEqualsLocallyBijective D]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective D]

/-- The objectwise constant-sheaf comparisons are natural in the coefficient object. -/
@[stacks 09BE "naturality of constant sheaf restriction"]
theorem constantSheafOverObjIso_naturality (U : C) {E F : D} (f : E ⟶ F) :
    (constantSheaf J D ⋙ J.overPullback D U).map f ≫
        (constantSheafOverObjIso (J := J) (D := D) U F).hom =
      (constantSheafOverObjIso (J := J) (D := D) U E).hom ≫
        (constantSheaf (J.over U) D).map f := sorry

/-- The constant-sheaf functor commutes with restriction to a slice, objectwise through the
canonical comparison `constantSheafOverObjIso`. -/
@[stacks 09BE "constant sheaf restriction comparison"]
noncomputable def constantSheafOverIso (U : C) :
    constantSheaf J D ⋙ J.overPullback D U ≅ constantSheaf (J.over U) D :=
  NatIso.ofComponents
    (fun E ↦ constantSheafOverObjIso (J := J) (D := D) U E)
    (fun f ↦ constantSheafOverObjIso_naturality (J := J) (D := D) U f)

end Constant

section ModuleInstances

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]

/-- Module categories are canonically preadditive. -/
instance moduleCatPreadditive :
    Preadditive (ModuleCat.{w} Λ) :=
  (inferInstance : Abelian (ModuleCat.{w} Λ)).toPreadditive

/-- Sheaves of modules inherit the canonical preadditive structure from their abelian structure. -/
instance sheafModulePreadditive :
    Preadditive (Sheaf J (ModuleCat.{w} Λ)) :=
  (inferInstance : Abelian (Sheaf J (ModuleCat.{w} Λ))).toPreadditive

/-- Sheaves of modules on a slice inherit the canonical preadditive structure. -/
instance sheafModuleOverPreadditive (U : C) :
    Preadditive (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  (inferInstance : Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))).toPreadditive

/-- The ambient sheaf category uses the preadditive zero-morphism instance. -/
instance sheafModuleHasZeroMorphisms :
    HasZeroMorphisms (Sheaf J (ModuleCat.{w} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- A slice sheaf category uses the preadditive zero-morphism instance. -/
instance sheafModuleOverHasZeroMorphisms (U : C) :
    HasZeroMorphisms (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The constant-sheaf functor on modules preserves zero morphisms. -/
instance constantSheafPreservesZeroMorphisms :
    (constantSheaf J (ModuleCat.{w} Λ)).PreservesZeroMorphisms := sorry

/-- The constant-sheaf functor on a slice preserves zero morphisms. -/
instance constantSheafOverPreservesZeroMorphisms (U : C) :
    (constantSheaf (J.over U) (ModuleCat.{w} Λ)).PreservesZeroMorphisms := sorry

/-- A family of additive constant-sheaf functors on slices yields the pointwise instance. -/
instance constantSheafOverAdditiveOfFamily
    [h : ∀ U : C, (constantSheaf (J.over U) (ModuleCat.{w} Λ)).Additive] (U : C) :
    (constantSheaf (J.over U) (ModuleCat.{w} Λ)).Additive :=
  h U

/-- A family of slice constant-sheaf functors preserving finite limits yields the pointwise
instance. -/
instance constantSheafOverPreservesFiniteLimitsOfFamily
    [h : ∀ U : C, PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))] (U : C) :
    PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ)) :=
  h U

/-- A family of slice constant-sheaf functors preserving finite colimits yields the pointwise
instance. -/
instance constantSheafOverPreservesFiniteColimitsOfFamily
    [h : ∀ U : C, PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))] (U : C) :
    PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ)) :=
  h U

/-- Restriction to a slice preserves zero morphisms whenever it is additive. -/
instance overPullbackPreservesZeroMorphisms (U : C)
    [(J.overPullback (ModuleCat.{w} Λ) U).Additive] :
    (J.overPullback (ModuleCat.{w} Λ) U).PreservesZeroMorphisms := sorry

/-- A family of additive slice restrictions yields the pointwise instance used by downstream
derived statements. -/
instance overPullbackAdditiveOfFamily
    [h : ∀ U : C, (J.overPullback (ModuleCat.{w} Λ) U).Additive] (U : C) :
    (J.overPullback (ModuleCat.{w} Λ) U).Additive :=
  h U

/-- A family of exact slice restrictions yields the pointwise finite-limit instance. -/
instance overPullbackPreservesFiniteLimitsOfFamily
    [h : ∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)] (U : C) :
    PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U) :=
  h U

/-- A family of exact slice restrictions yields the pointwise finite-colimit instance. -/
instance overPullbackPreservesFiniteColimitsOfFamily
    [h : ∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)] (U : C) :
    PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U) :=
  h U

end ModuleInstances

section Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, HasDerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
variable [(constantSheaf J (ModuleCat.{w} Λ)).Additive]
variable [PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} Λ))]
variable [PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, (constantSheaf (J.over U) (ModuleCat.{w} Λ)).Additive]
variable [∀ U : C, PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, (J.overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)]
variable [∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)]

/-- The canonical derived comparison between restricting an ambient constant derived object and the
constant derived object on the slice site. -/
@[stacks 09BE "derived constant sheaf restriction comparison"]
noncomputable def constantSheafOverDerivedIso (U : C) :
    (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory ⋙
        (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory ≅
      (constantSheaf (J.over U) (ModuleCat.{w} Λ)).mapDerivedCategory :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (constantSheaf J (ModuleCat.{w} Λ)))
      (ExactFunctor.of (J.overPullback (ModuleCat.{w} Λ) U))).symm ≪≫
    Functor.MapDerivedCategory.functorIso
      (constantSheafOverIso (J := J) (D := ModuleCat.{w} Λ) U)

end Derived

end CategoryTheory.Sheaf
