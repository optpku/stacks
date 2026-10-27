/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdealCompletion

/-!
# Quotient stages of weak-ideal completions
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

variable (A' : Type u) [CommRing A'] [Algebra A A']

/-- The affine scheme `Spec(A' ⧸ I A')` over `S`. -/
def quotientStage (I : WeakIdealOfDefinition A) : Over S :=
  Over.mk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal.map (algebraMap A A')))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ hA)

/-- The underlying scheme of `quotientStage` is `Spec(A' ⧸ I A')`. -/
theorem quotientStage_left (I : WeakIdealOfDefinition A) :
    (quotientStage hA A' I).left =
      Spec (.of (A' ⧸ I.ideal.map (algebraMap A A'))) := rfl

/-- The canonical ring map `A ⧸ I → A' ⧸ I A'`. -/
def quotientStageRingHom (I : WeakIdealOfDefinition A) :
    A ⧸ I.ideal →+* A' ⧸ I.ideal.map (algebraMap A A') :=
  Ideal.quotientMap (I.ideal.map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map

/-- `quotientStageRingHom` is `Ideal.quotientMap` along `algebraMap A A'`. -/
theorem quotientStageRingHom_eq (I : WeakIdealOfDefinition A) :
    quotientStageRingHom A' I =
      Ideal.quotientMap (I.ideal.map (algebraMap A A')) (algebraMap A A')
        Ideal.le_comap_map := rfl

/-- The quotient comparison commutes with the structure morphisms to the base scheme. -/
theorem quotientStageMap_comm (I : WeakIdealOfDefinition A) :
    Spec.map (CommRingCat.ofHom (quotientStageRingHom A' I)) ≫
      (stage A hA I).hom = (quotientStage hA A' I).hom := by
  change Spec.map (CommRingCat.ofHom (quotientStageRingHom A' I)) ≫
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal)) ≫ hA) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal.map (algebraMap A A')))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ hA
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    quotientStageRingHom, Ideal.quotientMap_comp_mk,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- The affine comparison `Spec(A' ⧸ I A') ⟶ Spec(A ⧸ I)` over `S`. -/
def quotientStageMap (I : WeakIdealOfDefinition A) :
    quotientStage hA A' I ⟶ stage A hA I :=
  Over.homMk (Spec.map (CommRingCat.ofHom (quotientStageRingHom A' I)))
    (quotientStageMap_comm hA A' I)

/-- The underlying scheme morphism of `quotientStageMap` is `Spec.map` of
`quotientStageRingHom`. -/
theorem quotientStageMap_left (I : WeakIdealOfDefinition A) :
    (quotientStageMap hA A' I).left =
      Spec.map (CommRingCat.ofHom (quotientStageRingHom A' I)) := rfl

/-- The kernel of the stage projection `(A')^∧ → A' ⧸ I A'`, bundled as a weak
ideal of definition of the completion. -/
def evalKer (I : WeakIdealOfDefinition A) :
    WeakIdealOfDefinition (weakIdealCompletion A A') :=
  WeakIdealOfDefinition.of (RingHom.ker (weakIdealCompletion.eval A A' I.isWeak))
    (weakIdealCompletion.isWeakIdealOfDefinition_eval_ker I.isWeak)

/-- `evalKer I` is the kernel of `eval` at the weak ideal `I`, and that kernel is
a weak ideal of definition. -/
theorem evalKer_spec (I : WeakIdealOfDefinition A) :
    (evalKer A' I).ideal = RingHom.ker (weakIdealCompletion.eval A A' I.isWeak) ∧
      TopologicalRing.Ideal.IsWeakIdealOfDefinition (evalKer A' I).ideal :=
  ⟨rfl, (evalKer A' I).property⟩

/-- The kernel-lift comparison commutes with the structure morphisms to the base scheme. -/
theorem evalKerStageMap_comm (I : WeakIdealOfDefinition A) :
    Spec.map (CommRingCat.ofHom
        (RingHom.kerLift (weakIdealCompletion.eval A A' I.isWeak))) ≫
      (stage (weakIdealCompletion A A') (specHom_weakIdealCompletion hA A')
        (evalKer A' I)).hom = (quotientStage hA A' I).hom := by
  change Spec.map (CommRingCat.ofHom
      (RingHom.kerLift (weakIdealCompletion.eval A A' I.isWeak))) ≫
    (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (RingHom.ker (weakIdealCompletion.eval A A' I.isWeak)))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap A (weakIdealCompletion A A'))) ≫ hA)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal.map (algebraMap A A')))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ hA
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom (weakIdealCompletion.eval A A' I.isWeak)) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap A (weakIdealCompletion A A'))) ≫ hA) = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (I.ideal.map (algebraMap A A'))).comp (algebraMap A A'))) ≫ hA = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- The comparison `Spec(A' ⧸ I A') ⟶ Spec((A')^∧ ⧸ ker eval)` induced by the
canonical lift of the stage projection. -/
def evalKerStageMap (I : WeakIdealOfDefinition A) :
    quotientStage hA A' I ⟶
      stage (weakIdealCompletion A A') (specHom_weakIdealCompletion hA A')
        (evalKer A' I) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (RingHom.kerLift (weakIdealCompletion.eval A A' I.isWeak))))
    (evalKerStageMap_comm hA A' I)

/-- The underlying scheme morphism of `evalKerStageMap` is `Spec.map` of
`RingHom.kerLift eval`. -/
theorem evalKerStageMap_left (I : WeakIdealOfDefinition A) :
    (evalKerStageMap hA A' I).left =
      Spec.map (CommRingCat.ofHom
        (RingHom.kerLift (weakIdealCompletion.eval A A' I.isWeak))) := rfl

/-- The comparison morphism `Spec(A' ⧸ I A') ⟶ Spf((A')^∧)` obtained by
identifying the source with the `evalKer` stage and applying the `spf` cocone. -/
def quotientStageι (I : WeakIdealOfDefinition A) :
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (yoneda.obj (quotientStage hA A' I)) ⟶
      spf (weakIdealCompletion A A') (specHom_weakIdealCompletion hA A') :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
      (yoneda.map (evalKerStageMap hA A' I)) ≫
    spfι (weakIdealCompletion A A') (specHom_weakIdealCompletion hA A')
      (evalKer A' I)

/-- `quotientStageι` is the sheafified `evalKerStageMap` postcomposed with the
`spf` cocone at `evalKer`. -/
theorem quotientStageι_eq (I : WeakIdealOfDefinition A) :
    quotientStageι hA A' I =
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (evalKerStageMap hA A' I)) ≫
        spfι (weakIdealCompletion A A') (specHom_weakIdealCompletion hA A')
          (evalKer A' I) := rfl

/-- The square
`Spec(A' ⧸ I A') ⟶ Spec(A ⧸ I)` over
`Spf((A')^∧) ⟶ Spf(A)` is a pullback. -/
theorem isPullback_quotientStage (I : WeakIdealOfDefinition A) :
    IsPullback
      ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (yoneda.map (quotientStageMap hA A' I)))
      (quotientStageι hA A' I) (spfι A hA I) (spfMap_weakIdealCompletion hA A') := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
