/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Ring.Ideal
public import stacks_project.Chap87.Example_87_19_11
public import stacks_project.Chap87.Example_87_24_7
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion

/-!
# Example 87.27.6

If `A` is weakly admissible over a scheme `S` and `K ⊂ A` is a closed ideal,
the weak-ideal completion `B = (A ⧸ K)^∧` yields a closed immersion
`Spf(B) ⟶ Spf(A)`. After a quasi-compact scheme `T ⟶ Spf(A)` factors through
`Spec(A ⧸ I)`, the fibre product is `T ×_{Spec(A ⧸ I)} Spec(A ⧸ (I + K))`.
The kernel of `A → B` is `K` because `K` is closed; the algebra map need not
be surjective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
  (K : Ideal A)

/-- The affine scheme `Spec(A ⧸ (I + K))` over `S`. -/
def specQuotSupStage (I : WeakIdealOfDefinition A) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal ⊔ K))) ≫ hA)

/-- The underlying scheme of `specQuotSupStage` is `Spec(A ⧸ (I + K))`. -/
theorem specQuotSupStage_left (I : WeakIdealOfDefinition A) :
    (specQuotSupStage hA K I).left = Spec (.of (A ⧸ (I.ideal ⊔ K))) :=
  sorry

/-- The affine comparison `Spec(A ⧸ (I + K)) ⟶ Spec(A ⧸ I)` over `S`. -/
def specQuotSupHom (I : WeakIdealOfDefinition A) :
    specQuotSupStage hA K I ⟶ stage A hA I :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (le_sup_left : I.ideal ≤ I.ideal ⊔ K))))
    sorry

/-- The underlying scheme morphism of `specQuotSupHom` is `Spec.map` of
`Ideal.Quotient.factor` along `I ≤ I + K`. -/
theorem specQuotSupHom_left (I : WeakIdealOfDefinition A) :
    (specQuotSupHom hA K I).left =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (le_sup_left : I.ideal ≤ I.ideal ⊔ K))) :=
  sorry

/-- `Spec(A ⧸ (I + K)) ⟶ Spec(A ⧸ I)` is a closed immersion of schemes. -/
instance instIsClosedImmersion_specQuotSupHom (I : WeakIdealOfDefinition A) :
    IsClosedImmersion (specQuotSupHom hA K I).left :=
  sorry

/-- The comparison `Spec(A ⧸ (I + K)) ⟶ Spec((A ⧸ K) ⧸ I (A ⧸ K))` over `S`
induced by `DoubleQuot.quotQuotEquivQuotSup`. -/
def specQuotSupToQuotientStage (I : WeakIdealOfDefinition A) :
    specQuotSupStage hA K I ⟶ quotientStage hA (A ⧸ K) I :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      ((DoubleQuot.quotQuotEquivQuotSup K I.ideal).trans
        (Ideal.quotEquivOfEq (sup_comm K I.ideal))).toRingHom))
    sorry

/-- The underlying scheme morphism of `specQuotSupToQuotientStage` is `Spec.map`
of the double-quotient identification with `A ⧸ (I + K)`. -/
theorem specQuotSupToQuotientStage_left (I : WeakIdealOfDefinition A) :
    (specQuotSupToQuotientStage hA K I).left =
      Spec.map (CommRingCat.ofHom
        ((DoubleQuot.quotQuotEquivQuotSup K I.ideal).trans
          (Ideal.quotEquivOfEq (sup_comm K I.ideal))).toRingHom) :=
  sorry

/-- The comparison morphism `Spec(A ⧸ (I + K)) ⟶ Spf((A ⧸ K)^∧)` obtained by
identifying the source with `quotientStage` and applying `quotientStageι`. -/
def specQuotSupStageι (I : WeakIdealOfDefinition A) :
    yoneda.obj (specQuotSupStage hA K I) ⟶
      (spf (weakIdealCompletion A (A ⧸ K))
        (specHom_weakIdealCompletion hA (A ⧸ K))).obj :=
  toSheafify (Scheme.fppfTopology.over S) (yoneda.obj (specQuotSupStage hA K I)) ≫
    Sheaf.homEquiv
      ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (specQuotSupToQuotientStage hA K I)) ≫
        quotientStageι hA (A ⧸ K) I)

/-- `specQuotSupStageι` is the sheafification unit postcomposed with the
sheafified double-quotient comparison and `quotientStageι`. -/
theorem specQuotSupStageι_eq (I : WeakIdealOfDefinition A) :
    specQuotSupStageι hA K I =
      toSheafify (Scheme.fppfTopology.over S)
          (yoneda.obj (specQuotSupStage hA K I)) ≫
        Sheaf.homEquiv
          ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
              (yoneda.map (specQuotSupToQuotientStage hA K I)) ≫
            quotientStageι hA (A ⧸ K) I) :=
  sorry

/-- The square `Spec(A ⧸ (I + K)) ⟶ Spec(A ⧸ I)` over
`Spf((A ⧸ K)^∧) ⟶ Spf(A)` is a pullback. -/
theorem isPullback_stage_spfMap_weakIdealCompletion_quotient
    (I : WeakIdealOfDefinition A) :
    IsPullback (yoneda.map (specQuotSupHom hA K I)) (specQuotSupStageι hA K I)
      (spfStageι hA I)
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hA (A ⧸ K))) :=
  sorry

/-- After a quasi-compact scheme `T ⟶ Spf(A)` factors through `Spec(A ⧸ I)`,
any pullback of `specQuotSupHom` along that factorization is a pullback of
`Spf((A ⧸ K)^∧) ⟶ Spf(A)`. -/
theorem isPullback_spfMap_weakIdealCompletion_quotient_of_factor
    {T : Over S} [CompactSpace T.left] {I : WeakIdealOfDefinition A}
    (g : yoneda.obj T ⟶ yoneda.obj (stage A hA I))
    {P : (Over S)ᵒᵖ ⥤ Type u} (fst : P ⟶ yoneda.obj T)
    (snd : P ⟶ yoneda.obj (specQuotSupStage hA K I))
    (hp : IsPullback fst snd g (yoneda.map (specQuotSupHom hA K I))) :
    IsPullback fst (snd ≫ specQuotSupStageι hA K I) (g ≫ spfStageι hA I)
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hA (A ⧸ K))) :=
  sorry

/-- Example 87.27.6 (1): `Spf((A ⧸ K)^∧) ⟶ Spf(A)` is a closed immersion of
formal algebraic spaces. -/
@[stacks 0ANR]
instance instClosedImmersion_spfMap_weakIdealCompletion_quotient
    [IsClosed (K : Set A)] :
    ClosedImmersion
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hA (A ⧸ K))) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace TopologicalRing.weakIdealCompletion

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]

/-- The kernel of `A → (A ⧸ K)^∧` is the closure of `K`. -/
theorem ker_algebraMap_eq_closure (K : Ideal A) :
    RingHom.ker (algebraMap A (weakIdealCompletion A (A ⧸ K))) = K.closure :=
  sorry

/-- Example 87.27.6 (2): the kernel of `A → (A ⧸ K)^∧` is `K` because `K` is
closed. In general `algebraMap A (weakIdealCompletion A (A ⧸ K))` need not be
surjective. -/
@[stacks 0ANR]
theorem ker_algebraMap_quotient (K : Ideal A) [IsClosed (K : Set A)] :
    RingHom.ker (algebraMap A (weakIdealCompletion A (A ⧸ K))) = K :=
  sorry

/-- Membership in the kernel of `A → (A ⧸ K)^∧` is membership in the closed
ideal `K`. -/
theorem mem_ker_algebraMap_quotient (K : Ideal A) [IsClosed (K : Set A)]
    {x : A} :
    x ∈ RingHom.ker (algebraMap A (weakIdealCompletion A (A ⧸ K))) ↔ x ∈ K :=
  sorry

end TopologicalRing.weakIdealCompletion
