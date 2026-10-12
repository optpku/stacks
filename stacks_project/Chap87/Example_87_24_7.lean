/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Example_87_19_11
public import stacks_project.Chap87.Lemma_87_9_4
public import stacks_project.Chap87.Lemma_87_24_2

/-!
# Example 87.24.7

If `A` is weakly admissible over a scheme `S` and `A → A'` is a finite-type
ring map, then the weak-ideal completion `(A')^∧` is weakly admissible and
`Spf((A')^∧) ⟶ Spf(A)` is representable, as in Example 87.19.11. A map from a
quasi-compact scheme into `Spf(A)` factors through some `Spec(A ⧸ I)` by
Lemma 87.9.4, the fibre product with `Spf((A')^∧)` is identified with the
affine comparison `Spec(A' ⧸ I A') ⟶ Spec(A ⧸ I)`, and therefore
`Spf((A')^∧) ⟶ Spf(A)` is of finite type.
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

/-- The functor-of-points cocone leg `yoneda.obj (Spec(A ⧸ I)) ⟶ Spf(A)`. -/
def spfStageι (I : WeakIdealOfDefinition A) :
    yoneda.obj (stage A hA I) ⟶ (spf A hA).obj :=
  toSheafify (Scheme.fppfTopology.over S) (yoneda.obj (stage A hA I)) ≫
    Sheaf.homEquiv (spfι A hA I)

/-- `spfStageι` is the sheafification unit postcomposed with the `spf` cocone
leg at `I`. -/
theorem spfStageι_eq (I : WeakIdealOfDefinition A) :
    spfStageι hA I =
      toSheafify (Scheme.fppfTopology.over S) (yoneda.obj (stage A hA I)) ≫
        Sheaf.homEquiv (spfι A hA I) :=
  sorry

/-- A morphism from a quasi-compact scheme over `S` into `Spf(A)` factors
through `Spec(A ⧸ I)` for some weak ideal of definition `I`, the `Spf`
specialization of Lemma 87.9.4. -/
theorem exists_factorThroughStage_spf {T : Over S} [CompactSpace T.left]
    (ξ : yoneda.obj T ⟶ (spf A hA).obj) :
    ∃ (I : WeakIdealOfDefinition A) (g : yoneda.obj T ⟶ yoneda.obj (stage A hA I)),
      g ≫ spfStageι hA I = ξ :=
  sorry

variable (A' : Type u) [CommRing A'] [Algebra A A']

/-- The affine scheme `Spec(A' ⧸ I A')` over `S`. -/
def quotientStage (I : WeakIdealOfDefinition A) : Over S :=
  Over.mk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal.map (algebraMap A A')))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ hA)

/-- The underlying scheme of `quotientStage` is `Spec(A' ⧸ I A')`. -/
theorem quotientStage_left (I : WeakIdealOfDefinition A) :
    (quotientStage hA A' I).left =
      Spec (.of (A' ⧸ I.ideal.map (algebraMap A A'))) :=
  sorry

/-- The canonical ring map `A ⧸ I → A' ⧸ I A'`. -/
def quotientStageRingHom (I : WeakIdealOfDefinition A) :
    A ⧸ I.ideal →+* A' ⧸ I.ideal.map (algebraMap A A') :=
  Ideal.quotientMap (I.ideal.map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map

/-- `quotientStageRingHom` is `Ideal.quotientMap` along `algebraMap A A'`. -/
theorem quotientStageRingHom_eq (I : WeakIdealOfDefinition A) :
    quotientStageRingHom A' I =
      Ideal.quotientMap (I.ideal.map (algebraMap A A')) (algebraMap A A')
        Ideal.le_comap_map :=
  sorry

/-- The affine comparison `Spec(A' ⧸ I A') ⟶ Spec(A ⧸ I)` over `S`. -/
def quotientStageMap (I : WeakIdealOfDefinition A) :
    quotientStage hA A' I ⟶ stage A hA I :=
  Over.homMk (Spec.map (CommRingCat.ofHom (quotientStageRingHom A' I))) sorry

/-- The underlying scheme morphism of `quotientStageMap` is `Spec.map` of
`quotientStageRingHom`. -/
theorem quotientStageMap_left (I : WeakIdealOfDefinition A) :
    (quotientStageMap hA A' I).left =
      Spec.map (CommRingCat.ofHom (quotientStageRingHom A' I)) :=
  sorry

/-- If `A → A'` is of finite type, then so is each stage map `A ⧸ I → A' ⧸ I A'`. -/
theorem finiteType_quotientStage [Algebra.FiniteType A A']
    (I : WeakIdealOfDefinition A) :
    Algebra.FiniteType (A ⧸ I.ideal) (A' ⧸ I.ideal.map (algebraMap A A')) :=
  sorry

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
  sorry

/-- The comparison `Spec(A' ⧸ I A') ⟶ Spec((A')^∧ ⧸ ker eval)` induced by the
canonical lift of the stage projection. -/
def evalKerStageMap (I : WeakIdealOfDefinition A) :
    quotientStage hA A' I ⟶
      stage (weakIdealCompletion A A') (specHom_weakIdealCompletion hA A')
        (evalKer A' I) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (RingHom.kerLift (weakIdealCompletion.eval A A' I.isWeak))))
    sorry

/-- The underlying scheme morphism of `evalKerStageMap` is `Spec.map` of
`RingHom.kerLift eval`. -/
theorem evalKerStageMap_left (I : WeakIdealOfDefinition A) :
    (evalKerStageMap hA A' I).left =
      Spec.map (CommRingCat.ofHom
        (RingHom.kerLift (weakIdealCompletion.eval A A' I.isWeak))) :=
  sorry

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
          (evalKer A' I) :=
  sorry

/-- Example 87.24.7 (1): the square
`Spec(A' ⧸ I A') ⟶ Spec(A ⧸ I)` over
`Spf((A')^∧) ⟶ Spf(A)` is a pullback. -/
@[stacks 0ANM]
theorem isPullback_quotientStage (I : WeakIdealOfDefinition A) :
    IsPullback
      ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (yoneda.map (quotientStageMap hA A' I)))
      (quotientStageι hA A' I) (spfι A hA I) (spfMap_weakIdealCompletion hA A') :=
  sorry

/-- Example 87.24.7 (2): if `A → A'` is of finite type, then
`Spf((A')^∧) ⟶ Spf(A)` is of finite type in the sense of Definition 87.24.1. -/
@[stacks 0ANM]
instance instFiniteType_spfMap_weakIdealCompletion [Algebra.FiniteType A A'] :
    FiniteType (spfMap_weakIdealCompletion hA A').hom :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
