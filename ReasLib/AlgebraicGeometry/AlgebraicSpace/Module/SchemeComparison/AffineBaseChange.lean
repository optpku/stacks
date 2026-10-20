/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square.Exact

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange

/-! # Affine étale and Zariski base-change comparisons -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The small étale object of `ofOver (Spec A)` associated to an open of `Spec A`. -/
private def specOpenSmallEtale {A : Type u} [CommRing A]
    (σA : Spec (CommRingCat.of A) ⟶ S) (U : (Over.mk σA).left.Opens) :
    smallEtaleSite (ofOver (Over.mk σA)) :=
  (schemeEtaleToSmallEtale (Over.mk σA)).obj
    ((smallEtaleToOpensRingedHom (Over.mk σA).left).base.obj U)

/-- Restriction of the affine base morphism to an open respects the structure maps. -/
private theorem specOpenPullbackHom_restrict_over {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  morphismRestrict s U ≫ VA.left.hom = VB.left.hom := sorry

/-- The restricted open morphism gives a commutative square of algebraic spaces. -/
private theorem specOpenPullbackHom_square {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  ofOverMap (Over.homMk (morphismRestrict s U)
      (specOpenPullbackHom_restrict_over σA σB hσ U)) ≫ (iA.obj VA).hom =
    (iB.obj VB).hom ≫ g := sorry

/-- The forward open comparison lies over the base spectrum. -/
private theorem specOpenPullbackHom_over {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  pullback.lift
      (ofOverMap (Over.homMk (morphismRestrict s U)
        (specOpenPullbackHom_restrict_over σA σB hσ U)) : ofOver VB.left ⟶ ofOver VA.left)
      (iB.obj VB).hom (specOpenPullbackHom_square σA σB hσ U) ≫
      ((spacesEtalePullback g).obj (iA.obj VA)).hom = (iB.obj VB).hom := sorry

/-- The morphism of spaces-étale objects over `Spec B` identifying the inverse-image open
with the fibre product of the source open along `Spec.map (algebraMap A B)`. -/
private def specOpenPullbackHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    (smallEtaleToSpaces (ofOver (Over.mk σB))).obj
        (specOpenSmallEtale σB
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ U)) ⟶
      (etaleBaseChange
          (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj
        (specOpenSmallEtale σA U) :=
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  MorphismProperty.Over.homMk
      (A := iB.obj VB)
      (B := (spacesEtalePullback g).obj (iA.obj VA))
      (pullback.lift
        (ofOverMap (Over.homMk (morphismRestrict s U) (specOpenPullbackHom_restrict_over σA σB hσ U)) : ofOver VB.left ⟶ ofOver VA.left)
        (iB.obj VB).hom
        (specOpenPullbackHom_square σA σB hσ U))
      (specOpenPullbackHom_over σA σB hσ U) ≫
    (smallEtaleInclusion_comp_spacesEtalePullback g).hom.app VA

/-- A point of the fibre product determines compatible scheme morphisms into the open and the base. -/
private theorem specOpenPullbackInv_square {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens)
    (T : (Over S)ᵒᵖ)
    (x : (Limits.pullback
      ((smallEtaleToSpaces (ofOver (Over.mk σA))).obj (specOpenSmallEtale σA U)).hom
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).functorOfPoints.obj T) :
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  let a := (pullback.fst (iA.obj VA).hom g).app T x
  let b := (pullback.snd (iA.obj VA).hom g).app T x
  a.left ≫ U.ι = b.left ≫ s := sorry

/-- The lift of a fibre-product point into the inverse-image open respects the structure map. -/
private theorem specOpenPullbackInv_lift_over {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens)
    (T : (Over S)ᵒᵖ)
    (x : (Limits.pullback
      ((smallEtaleToSpaces (ofOver (Over.mk σA))).obj (specOpenSmallEtale σA U)).hom
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).functorOfPoints.obj T) :
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  let a := (pullback.fst (iA.obj VA).hom g).app T x
  let b := (pullback.snd (iA.obj VA).hom g).app T x
  (isPullback_morphismRestrict s U).lift a.left b.left
      (specOpenPullbackInv_square σA σB hσ U T x) ≫ VB.left.hom = (unop T).hom := sorry

/-- The lift into an inverse-image open is natural in the test scheme. -/
private theorem specOpenPullbackInv_naturality {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  let app : ∀ T, (Limits.pullback (iA.obj VA).hom g).functorOfPoints.obj T ⟶
      (ofOver VB.left).functorOfPoints.obj T :=
    fun T ↦ TypeCat.ofHom fun x ↦
        let a := (pullback.fst (iA.obj VA).hom g).app T x
        let b := (pullback.snd (iA.obj VA).hom g).app T x
        Over.homMk (U := unop T) (V := VB.left)
          ((isPullback_morphismRestrict s U).lift a.left b.left
            (specOpenPullbackInv_square σA σB hσ U T x))
          (specOpenPullbackInv_lift_over σA σB hσ U T x)
  ∀ ⦃T T' : (Over S)ᵒᵖ⦄ (α : T ⟶ T'),
    (Limits.pullback (iA.obj VA).hom g).functorOfPoints.map α ≫ app T' =
      app T ≫ (ofOver VB.left).functorOfPoints.map α := sorry

/-- The reverse open comparison lies over the base spectrum. -/
private theorem specOpenPullbackInv_over {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  let reverse : Limits.pullback (iA.obj VA).hom g ⟶ ofOver VB.left :=
    { app := fun T ↦ TypeCat.ofHom fun x ↦
        let a := (pullback.fst (iA.obj VA).hom g).app T x
        let b := (pullback.snd (iA.obj VA).hom g).app T x
        Over.homMk (U := unop T) (V := VB.left)
          ((isPullback_morphismRestrict s U).lift a.left b.left
            (specOpenPullbackInv_square σA σB hσ U T x))
          (specOpenPullbackInv_lift_over σA σB hσ U T x)
      naturality := specOpenPullbackInv_naturality σA σB hσ U }
  reverse ≫ (iB.obj VB).hom = ((spacesEtalePullback g).obj (iA.obj VA)).hom := sorry

/-- The reverse spaces-étale comparison of `specOpenPullbackHom`. -/
private def specOpenPullbackInv {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    (etaleBaseChange
          (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj
        (specOpenSmallEtale σA U) ⟶
      (smallEtaleToSpaces (ofOver (Over.mk σB))).obj
        (specOpenSmallEtale σB
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ U)) :=
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleToSpaces (ofOver (Over.mk σB))
  let iA := smallEtaleToSpaces (ofOver (Over.mk σA))
  let reverse : Limits.pullback (iA.obj VA).hom g ⟶ ofOver VB.left :=
    { app := fun T ↦ TypeCat.ofHom fun x ↦
        let a := (pullback.fst (iA.obj VA).hom g).app T x
        let b := (pullback.snd (iA.obj VA).hom g).app T x
        Over.homMk (U := unop T) (V := VB.left)
          ((isPullback_morphismRestrict s U).lift a.left b.left
            (specOpenPullbackInv_square σA σB hσ U T x))
          (specOpenPullbackInv_lift_over σA σB hσ U T x)
      naturality := specOpenPullbackInv_naturality σA σB hσ U }
  (smallEtaleInclusion_comp_spacesEtalePullback g).inv.app VA ≫
    MorphismProperty.Over.homMk
      (A := (spacesEtalePullback g).obj (iA.obj VA))
      (B := iB.obj VB) reverse (specOpenPullbackInv_over σA σB hσ U)

/-- The explicit reverse open comparison is a right inverse of the forward comparison. -/
@[reassoc (attr := simp)]
private theorem specOpenPullbackHom_inv {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    specOpenPullbackHom σA σB hσ U ≫ specOpenPullbackInv σA σB hσ U = 𝟙 _ := sorry

/-- The explicit reverse open comparison is a left inverse of the forward comparison. -/
@[reassoc (attr := simp)]
private theorem specOpenPullbackInv_hom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    specOpenPullbackInv σA σB hσ U ≫ specOpenPullbackHom σA σB hσ U = 𝟙 _ := sorry

/-- `specOpenPullbackHom` has the explicitly constructed inverse open comparison. -/
private instance isIso_specOpenPullbackHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    IsIso (specOpenPullbackHom σA σB hσ U) :=
  ⟨⟨specOpenPullbackInv σA σB hσ U,
    specOpenPullbackHom_inv σA σB hσ U, specOpenPullbackInv_hom σA σB hσ U⟩⟩

/-- Type-valued component of the `toScheme` direct-image comparison at an open of `Spec A`. -/
private def toScheme_pushforwardUnderlyingApp {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) (U : ((Over.mk σA).left.Opens)ᵒᵖ) :
    ((Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
        ((toScheme (Over.mk σA)).obj
          ((pushforward
              (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N))).obj.obj
      U ⟶
      ((Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
        ((Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
          ((toScheme (Over.mk σB)).obj N))).obj.obj U :=
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VA := specOpenSmallEtale σA (unop U)
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ unop U)
  let Nty :=
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf (ofOver (Over.mk σB)))).obj N
  ((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom g)).hom.app N).hom.app
      (op VA) ≫
    (EtaleTopos.extensionEvaluation (ofOver (Over.mk σB)) Nty
      (U := VB) (W := (etaleBaseChange g).obj VA)
      (specOpenPullbackHom σA σB hσ (unop U)) :
        ((typePushforward g).obj Nty).obj.obj (op VA) ⟶ Nty.obj.obj (op VB))

/-- The direct-image comparison on underlying sections commutes with restriction. -/
private theorem toScheme_pushforwardUnderlying_naturality {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
  ∀ ⦃U V : ((Over.mk σA).left.Opens)ᵒᵖ⦄ (α : U ⟶ V),
    ((Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
      ((toScheme (Over.mk σA)).obj
      ((pushforward (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N))).obj.map α ≫ toScheme_pushforwardUnderlyingApp σA σB hσ N V =
      toScheme_pushforwardUnderlyingApp σA σB hσ N U ≫
        ((Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((toScheme (Over.mk σB)).obj N))).obj.map α := sorry

/-- Type-valued sheaf morphism of the `toScheme` direct-image comparison. -/
private def toScheme_pushforwardUnderlying {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
      ((toScheme (Over.mk σA)).obj
        ((pushforward
            (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N)) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
        ((Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
          ((toScheme (Over.mk σB)).obj N)) :=
  { hom :=
      { app := fun U ↦ toScheme_pushforwardUnderlyingApp σA σB hσ N U
        naturality := toScheme_pushforwardUnderlying_naturality σA σB hσ N } }

/-- The direct-image comparison preserves addition of sections. -/
private theorem toScheme_pushforwardHom_map_add {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
  ∀ U (x y : ((toScheme (Over.mk σA)).obj
      ((pushforward (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N)).val.obj U),
    Sheaf.InternalModule.underlyingApp (Over.mk σA).left.ringCatSheaf
      (toScheme_pushforwardUnderlying σA σB hσ N) U (x + y) =
      Sheaf.InternalModule.underlyingApp (Over.mk σA).left.ringCatSheaf
      (toScheme_pushforwardUnderlying σA σB hσ N) U x + Sheaf.InternalModule.underlyingApp (Over.mk σA).left.ringCatSheaf
      (toScheme_pushforwardUnderlying σA σB hσ N) U y := sorry

/-- The direct-image comparison respects scalar multiplication of sections. -/
private theorem toScheme_pushforwardHom_map_smul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
  ∀ U (r : (Over.mk σA).left.ringCatSheaf.obj.obj U)
      (x : ((toScheme (Over.mk σA)).obj
      ((pushforward (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N)).val.obj U),
    Sheaf.InternalModule.underlyingApp (Over.mk σA).left.ringCatSheaf
      (toScheme_pushforwardUnderlying σA σB hσ N) U (r • x) = r • Sheaf.InternalModule.underlyingApp (Over.mk σA).left.ringCatSheaf
      (toScheme_pushforwardUnderlying σA σB hσ N) U x := sorry

/-- Direct-image comparison of `toScheme` against affine spectrum pushforward. -/
@[no_expose] def toScheme_pushforwardHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
    (toScheme (Over.mk σA)).obj
        ((pushforward
            (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N) ⟶
      (Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        ((toScheme (Over.mk σB)).obj N) :=
  Sheaf.InternalModule.homOfUnderlying (Over.mk σA).left.ringCatSheaf
    (toScheme_pushforwardUnderlying σA σB hσ N)
    (toScheme_pushforwardHom_map_add σA σB hσ N)
    (toScheme_pushforwardHom_map_smul σA σB hσ N)

/-- The direct-image comparison is natural in the coefficient module. -/
private theorem toScheme_pushforwardNatTrans_naturality {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB) :
  ∀ ⦃N N' : (ofOver (Over.mk σB)).Modules⦄ (α : N ⟶ N'),
    (toScheme (Over.mk σA)).map
        ((pushforward (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).map α) ≫
      toScheme_pushforwardHom σA σB hσ N' =
    toScheme_pushforwardHom σA σB hσ N ≫
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
        ((toScheme (Over.mk σB)).map α) := sorry

/-- Natural transformation of the direct-image `toScheme` square. -/
private def toScheme_pushforwardNatTrans {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB) :
    pushforward (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ) ⋙
        toScheme (Over.mk σA) ⟶
      toScheme (Over.mk σB) ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  { app := fun N ↦ toScheme_pushforwardHom σA σB hσ N
    naturality := toScheme_pushforwardNatTrans_naturality σA σB hσ }

/-- The comparison `s^* (toScheme G) ⟶ toScheme (g^* G)` of modules on `Spec B`, as the
left-adjoint mate of `toScheme_pushforwardNatTrans`. -/
@[no_expose] def toScheme_pullbackHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (G : (ofOver (Over.mk σA)).Modules) :
    (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((toScheme (Over.mk σA)).obj G) ⟶
    (toScheme (Over.mk σB)).obj
      ((pullback (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj G) :=
  ((mateEquiv
        (pullbackPushforwardAdjunction
          (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
        (Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap A B))))).symm
      (toScheme_pushforwardNatTrans σA σB hσ)).app G

/-- Pullback commutes with restriction to the Zariski site on quasi-coherent modules. -/
instance isIso_toScheme_pullbackHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (G : (ofOver (Over.mk σA)).Modules) [G.IsQuasicoherent] :
    IsIso (toScheme_pullbackHom σA σB hσ G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
