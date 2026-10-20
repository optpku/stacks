/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.PlusModel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.CategoryTheory.Pro.Presentation
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ModuleDerived
open AlgebraicGeometry.Scheme.Modules
open Scheme.Compactification.Of
open DerivedCategory
open DerivedCategory.Bounded.CohomologyIn
open DerivedCategory.Plus
open DerivedCategory.Plus.CohomologyIn
open RingedSpace
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

/-- Module sheaves on a scheme carry the standard derived category. -/
noncomputable instance hasDerivedCategory_schemeModules (X : Scheme.{u}) :
    HasDerivedCategory (Mod(X.ringCatSheaf)) :=
  schemeModulesHasDerivedCategory X

variable {C : Type*} [Category.{u + 1} C] {D : Type*} [Category.{u + 1} D]

/-- Sequential mapping of inverse systems indexed by `OrderDual ℕ+` along a functor,
obtained by whiskering and then forming the associated pro-object. -/
noncomputable def mapSequentialPro (F : C ⥤ D) :
    ((OrderDual ℕ+) ⥤ C) ⥤ Pro D :=
  (Functor.whiskeringRight (OrderDual ℕ+) C D).obj F ⋙
    @Pro.lim D _ (OrderDual ℕ+) _ _ _ _

/-- The Hom bifunctor represented by a compact-support pushforward valued in the
pro-category of coherent bounded-below derived objects. -/
noncomputable def compactSupportHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S}
    (Rf : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])ᵒᵖ ×
        D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] ⥤ Type (u + 1) :=
  (Rf.op.prod
      (Pro.yoneda : D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] ⥤
        Pro D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])) ⋙
    Functor.hom (Pro D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])

/-- Objectwise, `compactSupportHom` is the Hom type from `Rf.obj K` to the
constant pro-object on `L`. -/
theorem compactSupportHom_obj
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S}
    (Rf : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (compactSupportHom Rf).obj (op K, L) =
      (Rf.obj K ⟶ Pro.yoneda.obj L) := sorry

/-- The Hom bifunctor into the coherent bounded-below upper-shriek model attached to
a compactification and a compatible right-adjoint model. -/
noncomputable def upperShriekHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (Over.hom (Under.right P.obj))) :
    (Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])ᵒᵖ ×
        D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] ⥤ Type (u + 1) :=
  ((Bounded.CohomologyIn.ambient
      (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).op.prod
        (upperShriekCoherentPlus f P A.right A.adjunction A.plus
          A.compatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))) ⋙
    Functor.hom (DerivedCategory (Over.left X.obj).Modules)

/-- Objectwise, `upperShriekHom` is the ambient derived Hom into the compactification-based
upper shriek. -/
theorem upperShriekHom_obj
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (Over.hom (Under.right P.obj)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (upperShriekHom f P A).obj (op K, L) =
      ((Bounded.CohomologyIn.ambient
          (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K ⟶
        (Plus.CohomologyIn.ambient
          (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj
          ((upperShriekCoherentPlus f P A.right A.adjunction A.plus
            A.compatibility).obj L)) := sorry

/-- Compatibility view of `upperShriekHom` unpacking the right-adjoint model into its
component functors. -/
noncomputable def shriekHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (a : DerivedQCoh (Over.left Y.obj) ⥤
      DerivedQCoh (Over.left (Under.right P.obj)))
    (aAdjunction :
      DerivedQCoh.pushforwardCohomologyIn (Over.hom (Under.right P.obj)) ⊣ a)
    (aPlus : DerivedQCoh.Plus (Over.left Y.obj) ⥤
      DerivedQCoh.Plus (Over.left (Under.right P.obj)))
    (aPlusCompatibility :
      aPlus ⋙ Plus.CohomologyIn.ambient
          (quasiCoherentModuleProperty (Over.left (Under.right P.obj))) ≅
        Plus.CohomologyIn.toUnbounded
            (quasiCoherentModuleProperty (Over.left Y.obj)) ⋙
          a ⋙ DerivedQCoh.inclusion (Over.left (Under.right P.obj))) :
    (Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])ᵒᵖ ×
        D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] ⥤ Type (u + 1) :=
  ((Bounded.CohomologyIn.ambient
      (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).op.prod
        (upperShriekCoherentPlus f P a aAdjunction aPlus
          aPlusCompatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))) ⋙
    Functor.hom (DerivedCategory (Over.left X.obj).Modules)

/-- Objectwise, the compatibility view `shriekHom` has the expected derived Hom type. -/
theorem shriekHom_obj
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (a : DerivedQCoh (Over.left Y.obj) ⥤
      DerivedQCoh (Over.left (Under.right P.obj)))
    (aAdjunction :
      DerivedQCoh.pushforwardCohomologyIn (Over.hom (Under.right P.obj)) ⊣ a)
    (aPlus : DerivedQCoh.Plus (Over.left Y.obj) ⥤
      DerivedQCoh.Plus (Over.left (Under.right P.obj)))
    (aPlusCompatibility :
      aPlus ⋙ Plus.CohomologyIn.ambient
          (quasiCoherentModuleProperty (Over.left (Under.right P.obj))) ≅
        Plus.CohomologyIn.toUnbounded
            (quasiCoherentModuleProperty (Over.left Y.obj)) ⋙
          a ⋙ DerivedQCoh.inclusion (Over.left (Under.right P.obj)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (shriekHom f P a aAdjunction aPlus aPlusCompatibility).obj (op K, L) =
      ((Bounded.CohomologyIn.ambient
          (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K ⟶
        (Plus.CohomologyIn.ambient
          (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj
          ((upperShriekCoherentPlus f P a aAdjunction aPlus
            aPlusCompatibility).obj L)) := sorry

/-- Bounded coherent derived objects remain coherent after being viewed as bounded-below. -/
theorem coherentBoundedToPlus_obj_mem
    {X : Scheme.{u}}
    (K : @DerivedCategory.Bounded.CohomologyIn X.Modules _ _
      (schemeModulesHasDerivedCategory X)
      (SheafOfModules.isCoherent X.ringCatSheaf)) :
    @DerivedCategory.Plus.cohomologyIn X.Modules _ _
      (schemeModulesHasDerivedCategory X)
      (SheafOfModules.isCoherent X.ringCatSheaf)
      (((@DerivedCategory.Bounded.cohomologyIn X.Modules _ _
            (schemeModulesHasDerivedCategory X)
            (SheafOfModules.isCoherent X.ringCatSheaf)).ι ⋙
          ObjectProperty.ιOfLE
            (inf_le_left :
              (@DerivedCategory.TStructure.t X.Modules _ _
                (schemeModulesHasDerivedCategory X)).bounded ≤
                (@DerivedCategory.TStructure.t X.Modules _ _
                  (schemeModulesHasDerivedCategory X)).plus)).obj K) := sorry

/-- The canonical embedding of bounded coherent derived objects into bounded-below
coherent derived objects. -/
noncomputable def coherentBoundedToPlus (X : Scheme.{u}) :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
      D⁺[SheafOfModules.isCoherent X.ringCatSheaf] :=
  (@DerivedCategory.Plus.cohomologyIn X.Modules _ _
      (schemeModulesHasDerivedCategory X)
      (SheafOfModules.isCoherent X.ringCatSheaf)).lift
    ((@DerivedCategory.Bounded.cohomologyIn X.Modules _ _
        (schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf)).ι ⋙
      ObjectProperty.ιOfLE
        (inf_le_left :
          (@DerivedCategory.TStructure.t X.Modules _ _
            (schemeModulesHasDerivedCategory X)).bounded ≤
            (@DerivedCategory.TStructure.t X.Modules _ _
              (schemeModulesHasDerivedCategory X)).plus))
    coherentBoundedToPlus_obj_mem

/-- Proper derived pushforward of a bounded-below coherent object remains coherent. -/
theorem compactSupportPushforward_obj_mem
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} {f : X ⟶ Y}
    (P : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (K : Dᵇ[SheafOfModules.isCoherent
      (Over.left (Under.right P.obj)).ringCatSheaf]) :
    DerivedCategory.Plus.cohomologyIn
        (SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf)
      ((moduleDerivedPushforwardPlus
          (Over.hom (Under.right P.obj)).toShHom).obj
        ((Plus.cohomologyIn
            (SheafOfModules.isCoherent
              (Over.left (Under.right P.obj)).ringCatSheaf)).ι.obj
          ((coherentBoundedToPlus (Over.left (Under.right P.obj))).obj K))) := sorry

/-- Sequential Deligne towers of chosen extension-by-zero presentations, as a functor
into inverse systems indexed by `OrderDual ℕ+`. -/
noncomputable def compactSupportDeligneTower
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} {f : X ⟶ Y}
    (P : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)) :
    Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      ((OrderDual ℕ+) ⥤
        Dᵇ[SheafOfModules.isCoherent
          (Over.left (Under.right P.obj)).ringCatSheaf]) where
  obj K :=
    @DeligneSystem.boundedTower _ _
      (Compactification.Of.ι P)
      (Compactification.Of.instAmbientIsNoetherian P)
      (FiniteTypeSeparatedOver.instIsNoetherian X)
      (Compactification.Of.instIsOpenImmersion (Over.left Y.obj)
        (Over.mk f.hom.left) P)
      (@DeligneSystem.extension _ _
        (Compactification.Of.ι P)
        (Compactification.Of.instAmbientIsNoetherian P)
        (FiniteTypeSeparatedOver.instIsNoetherian X)
        (Compactification.Of.instIsOpenImmersion (Over.left Y.obj)
          (Over.mk f.hom.left) P) K)
  map {_ _} _ := 0
  map_id := sorry
  map_comp := sorry

/-- Compactly supported derived pushforward along a finite-type separated morphism,
formed as sequential `Pro.lim` of the Deligne extension-by-zero tower along a
compactification, whiskered with the embedding into bounded-below coherent objects
and proper derived pushforward. -/
noncomputable def compactSupportPushforward
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)) :
    Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] :=
  compactSupportDeligneTower (f := f) P ⋙
    mapSequentialPro
      ((DerivedCategory.Plus.cohomologyIn
          (SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf)).lift
        (coherentBoundedToPlus (Over.left (Under.right P.obj)) ⋙
          (Plus.cohomologyIn
              (SheafOfModules.isCoherent
                (Over.left (Under.right P.obj)).ringCatSheaf)).ι ⋙
            moduleDerivedPushforwardPlus
              (Over.hom (Under.right P.obj)).toShHom)
        (fun K ↦ compactSupportPushforward_obj_mem P K))

/-- Compactly supported derived pushforward is left adjoint to compactification-based
coherent bounded-below upper shriek, in the sense that their Hom bifunctors are
naturally isomorphic. -/
theorem homIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (Over.hom (Under.right P.obj))) :
    Nonempty
      (compactSupportHom (compactSupportPushforward f P) ≅
        upperShriekHom f P A) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
