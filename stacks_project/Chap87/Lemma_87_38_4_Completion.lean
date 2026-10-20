module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Constructions
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Definition_87_7_1_WeaklyAdic
public import stacks_project.Chap87.Example_87_13_2_FormalSpectrum
public import stacks_project.Chap87.Lemma_87_14_6_PowerStages

/-!
# Affine formal completions along a closed subscheme

For `X = Spec(A)` over `S` and a closed subscheme `Z = Spec(A ⧸ I)`, the
functor-of-points completion `X^∧_Z` is `spfAdicCompletion`. This module
supplies the inverse-limit and `I`-adic topologies on `AdicCompletion I A`,
the comparison morphisms into `spf`, and the weakly adic type of an affine
formal algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A weakly adic ring is weakly admissible: a weakly adic ideal is a weak ideal
of definition, and the completeness and separation hypotheses match. -/
instance instIsWeaklyAdmissibleRing_of_isWeaklyAdicRing {R : Type u}
    [CommRing R] [TopologicalSpace R] [TopologicalRing.IsWeaklyAdicRing R] :
    TopologicalRing.IsWeaklyAdmissibleRing R :=
  sorry

section InverseLimitAndAdic

variable {A : Type u} [CommRing A]

/-- `AdicCompletion I A` equipped with the inverse-limit topology of the discrete
stages `A ⧸ I ^ n`. -/
def withLimitTopology (I : Ideal A) : Type u :=
  AdicCompletion I A

/-- `AdicCompletion I A` equipped with the `I`-adic topology of the extended
ideal. -/
def withAdicTopology (I : Ideal A) : Type u :=
  AdicCompletion I A

/-- The inverse-limit topology on `AdicCompletion I A`, induced from the product
of discrete topologies on the compatible families in `Π n, A ⧸ I ^ n`. -/
def inverseLimitVal (I : Ideal A) :
    AdicCompletion I A → ∀ n : ℕ, A ⧸ (I ^ n • ⊤ : Submodule A A) :=
  fun x => x.val

/-- The inverse-limit completion carries the ring structure of
`AdicCompletion I A`. -/
instance instCommRing_withLimitTopology (I : Ideal A) :
    CommRing (withLimitTopology I) :=
  inferInstanceAs (CommRing (AdicCompletion I A))

/-- The inverse-limit completion is an `A`-algebra via the canonical map
into `AdicCompletion I A`. -/
instance instAlgebra_withLimitTopology (I : Ideal A) :
    Algebra A (withLimitTopology I) :=
  inferInstanceAs (Algebra A (AdicCompletion I A))

/-- The topology on `withLimitTopology I` is the inverse-limit topology. -/
instance instTopologicalSpace_withLimitTopology (I : Ideal A) :
    TopologicalSpace (withLimitTopology I) :=
  TopologicalSpace.induced (inverseLimitVal I)
    (@Pi.topologicalSpace ℕ (fun n : ℕ => A ⧸ (I ^ n • ⊤ : Submodule A A))
      (fun _ => ⊥))

/-- The `I`-adic completion carries the ring structure of
`AdicCompletion I A`. -/
instance instCommRing_withAdicTopology (I : Ideal A) :
    CommRing (withAdicTopology I) :=
  inferInstanceAs (CommRing (AdicCompletion I A))

/-- The `I`-adic completion is an `A`-algebra via the canonical map into
`AdicCompletion I A`. -/
instance instAlgebra_withAdicTopology (I : Ideal A) :
    Algebra A (withAdicTopology I) :=
  inferInstanceAs (Algebra A (AdicCompletion I A))

/-- The topology on `withAdicTopology I` is the adic topology of the
extended ideal. -/
instance instTopologicalSpace_withAdicTopology (I : Ideal A) :
    TopologicalSpace (withAdicTopology I) :=
  (Ideal.map (algebraMap A (withAdicTopology I)) I).adicTopology

/-- The inverse-limit topology on `AdicCompletion I A` is weakly adic. -/
instance instIsWeaklyAdicRing_withLimitTopology (I : Ideal A) :
    TopologicalRing.IsWeaklyAdicRing (withLimitTopology I) :=
  sorry

/-- The canonical ring map `A →+* AdicCompletion I A`, as a map into the
inverse-limit topology. -/
def ofLimit (I : Ideal A) : A →+* withLimitTopology I :=
  algebraMap A (withLimitTopology I)

/-- The canonical ring map `A →+* AdicCompletion I A`, as a map into the
`I`-adic topology. -/
def ofAdic (I : Ideal A) : A →+* withAdicTopology I :=
  algebraMap A (withAdicTopology I)

/-- The extended ideal `I · AdicCompletion I A` on the inverse-limit completion. -/
def evalIdeal (I : Ideal A) : Ideal (withLimitTopology I) :=
  Ideal.map (ofLimit I) I

/-- The extended ideal `I · AdicCompletion I A` on the `I`-adic completion. -/
def evalIdealAdic (I : Ideal A) : Ideal (withAdicTopology I) :=
  Ideal.map (ofAdic I) I

/-- Evaluation of an inverse-limit family at the stage `A ⧸ I ^ (n + 1)`. -/
def evalRingHom (I : Ideal A) (n : ℕ) :
    withLimitTopology I →+* A ⧸ I ^ (n + 1) :=
  (AdicCompletion.evalₐ I (n + 1)).toRingHom

/-- Evaluation of an `I`-adic family at the stage `A ⧸ I ^ (n + 1)`. -/
def evalRingHomAdic (I : Ideal A) (n : ℕ) :
    withAdicTopology I →+* A ⧸ I ^ (n + 1) :=
  (AdicCompletion.evalₐ I (n + 1)).toRingHom

/-- Evaluation `AdicCompletion I A →+* A ⧸ I ^ (n + 1)` is surjective. -/
theorem evalRingHom_surjective (I : Ideal A) (n : ℕ) :
    Function.Surjective (evalRingHom I n) :=
  sorry

/-- Evaluation in the `I`-adic topology is surjective. -/
theorem evalRingHomAdic_surjective (I : Ideal A) (n : ℕ) :
    Function.Surjective (evalRingHomAdic I n) :=
  sorry

/-- The kernel of evaluation at stage `n`, as an ideal of the inverse-limit
completion. -/
def evalKernel (I : Ideal A) (n : ℕ) : Ideal (withLimitTopology I) :=
  RingHom.ker (evalRingHom I n)

/-- The kernel of evaluation at stage `n`, as an ideal of the `I`-adic
completion. -/
def evalKernelAdic (I : Ideal A) (n : ℕ) : Ideal (withAdicTopology I) :=
  RingHom.ker (evalRingHomAdic I n)

/-- Evaluation kernels are weak ideals of definition for the inverse-limit
topology. -/
theorem evalKernel_isWeakIdealOfDefinition (I : Ideal A) (n : ℕ) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (evalKernel I n) :=
  sorry

/-- Evaluation kernels are weak ideals of definition for the `I`-adic topology. -/
theorem evalKernelAdic_isWeakIdealOfDefinition (I : Ideal A) (n : ℕ) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (evalKernelAdic I n) :=
  sorry

/-- The evaluation kernel at stage `n`, bundled as a weak ideal of definition
of the inverse-limit completion. -/
def evalWeakIdeal (I : Ideal A) (n : ℕ) : WeakIdealOfDefinition (withLimitTopology I) :=
  WeakIdealOfDefinition.of (evalKernel I n) (evalKernel_isWeakIdealOfDefinition I n)

/-- The evaluation kernel at stage `n`, bundled as a weak ideal of definition
of the `I`-adic completion. -/
def evalWeakIdealAdic (I : Ideal A) (n : ℕ) : WeakIdealOfDefinition (withAdicTopology I) :=
  WeakIdealOfDefinition.of (evalKernelAdic I n) (evalKernelAdic_isWeakIdealOfDefinition I n)

/-- The structure morphism of `Spec` of the inverse-limit completion over `S`. -/
def structureHomCompletion {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) : Spec (.of (withLimitTopology I)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (ofLimit I)) ≫ structureHom

/-- The structure morphism of `Spec` of the `I`-adic completion over `S`. -/
def structureHomCompletionAdic {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) : Spec (.of (withAdicTopology I)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (ofAdic I)) ≫ structureHom

/-- The comparison of affine stages `Spec(A ⧸ I ^ (n + 1)) ⟶ Spec(B ⧸ ker(evalₙ))`
over `S`, where `B` carries the inverse-limit topology. -/
def powerStageToLimitStage {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (n : ℕ) :
    powerStage structureHom I n ⟶
      stage (withLimitTopology I) (structureHomCompletion structureHom I)
        (evalWeakIdeal I n) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (RingHom.kerLift (evalRingHom I n)))) sorry

/-- The comparison of affine stages `Spec(A ⧸ I ^ (n + 1)) ⟶ Spec(A^∧ ⧸ ker(evalₙ))`
over `S`, where `A^∧` carries the `I`-adic topology. -/
def powerStageToAdicStage {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (n : ℕ) :
    powerStage structureHom I n ⟶
      stage (withAdicTopology I) (structureHomCompletionAdic structureHom I)
        (evalWeakIdealAdic I n) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (RingHom.kerLift (evalRingHomAdic I n))))
    sorry

/-- The cocone of power stages valued in `spf` of the inverse-limit completion. -/
def toSpfLimitCocone {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) :
    Cocone (powerThickenings structureHom I ⋙ yoneda) where
  pt := spf (withLimitTopology I) (structureHomCompletion structureHom I)
  ι :=
    { app n :=
        yoneda.map (powerStageToLimitStage structureHom I n) ≫
          colimit.ι
            (thickenings (withLimitTopology I)
              (structureHomCompletion structureHom I) ⋙ yoneda)
            (evalWeakIdeal I n)
      naturality := sorry }

/-- The comparison `X^∧_Z ⟶ Spf(B)` for `B = lim A ⧸ I ^ n` with the
inverse-limit topology. -/
def toSpfLimit {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletion structureHom I ⟶
      spf (withLimitTopology I) (structureHomCompletion structureHom I) :=
  colimit.desc (powerThickenings structureHom I ⋙ yoneda)
    (toSpfLimitCocone structureHom I)

/-- Restricting `toSpfLimit` to the `n`th power stage recovers the stage
comparison followed by the `spf` cocone leg. -/
theorem toSpfLimit_ι {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (n : ℕ) :
    spfAdicCompletionι structureHom I n ≫ toSpfLimit structureHom I =
      yoneda.map (powerStageToLimitStage structureHom I n) ≫
        colimit.ι
          (thickenings (withLimitTopology I)
            (structureHomCompletion structureHom I) ⋙ yoneda)
          (evalWeakIdeal I n) :=
  sorry

/-- The comparison `toSpfLimit` is an isomorphism. -/
theorem isIso_toSpfLimit {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) : IsIso (toSpfLimit structureHom I) :=
  sorry

/-- The cocone of power stages valued in the Yoneda colimit of `I`-adic
weak-ideal thickenings. -/
def toSpfAdicCocone {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) :
    Cocone (powerThickenings structureHom I ⋙ yoneda) where
  pt :=
    colimit
      (thickenings (withAdicTopology I) (structureHomCompletionAdic structureHom I) ⋙
        yoneda)
  ι :=
    { app n :=
        yoneda.map (powerStageToAdicStage structureHom I n) ≫
          colimit.ι
            (thickenings (withAdicTopology I)
              (structureHomCompletionAdic structureHom I) ⋙ yoneda)
            (evalWeakIdealAdic I n)
      naturality := sorry }

/-- The comparison `X^∧_Z ⟶ Spf(A^∧)` into the Yoneda colimit of `Spec` of
quotients of the `I`-adic completion. -/
def toSpfAdic {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletion structureHom I ⟶
      colimit
        (thickenings (withAdicTopology I) (structureHomCompletionAdic structureHom I) ⋙
          yoneda) :=
  colimit.desc (powerThickenings structureHom I ⋙ yoneda)
    (toSpfAdicCocone structureHom I)

/-- Restricting `toSpfAdic` to the `n`th power stage recovers the stage
comparison followed by the adic `spf` cocone leg. -/
theorem toSpfAdic_ι {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (n : ℕ) :
    spfAdicCompletionι structureHom I n ≫ toSpfAdic structureHom I =
      yoneda.map (powerStageToAdicStage structureHom I n) ≫
        colimit.ι
          (thickenings (withAdicTopology I)
            (structureHomCompletionAdic structureHom I) ⋙ yoneda)
          (evalWeakIdealAdic I n) :=
  sorry

/-- When the `I`-adic topology is weakly admissible, the target of `toSpfAdic`
is `spf` of that topology. -/
theorem toSpfAdic_eq_spf {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) [TopologicalRing.IsWeaklyAdmissibleRing (withAdicTopology I)] :
    colimit
        (thickenings (withAdicTopology I) (structureHomCompletionAdic structureHom I) ⋙
          yoneda) =
      spf (withAdicTopology I) (structureHomCompletionAdic structureHom I) :=
  sorry

/-- The cocone of power stages valued in `spf` of the `I`-adic completion. -/
def toSpfAdicSpfCocone {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A)
    [hAdm : TopologicalRing.IsWeaklyAdmissibleRing (withAdicTopology I)] :
    Cocone (powerThickenings structureHom I ⋙ yoneda) where
  pt := spf (withAdicTopology I) (structureHomCompletionAdic structureHom I)
  ι :=
    { app n :=
        yoneda.map (powerStageToAdicStage structureHom I n) ≫
          colimit.ι
            (thickenings (withAdicTopology I)
              (structureHomCompletionAdic structureHom I) ⋙ yoneda)
            (evalWeakIdealAdic I n)
      naturality := sorry }

/-- The comparison `X^∧_Z ⟶ Spf(A^∧)` into the formal spectrum of the `I`-adic
completion. -/
def toSpfAdicSpf {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A)
    [hAdm : TopologicalRing.IsWeaklyAdmissibleRing (withAdicTopology I)] :
    spfAdicCompletion structureHom I ⟶
      spf (withAdicTopology I) (structureHomCompletionAdic structureHom I) :=
  colimit.desc (powerThickenings structureHom I ⋙ yoneda)
    (toSpfAdicSpfCocone structureHom I)

/-- Restricting `toSpfAdicSpf` to the `n`th power stage recovers the stage
comparison followed by the adic `spf` cocone leg. -/
theorem toSpfAdicSpf_ι {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A)
    [hAdm : TopologicalRing.IsWeaklyAdmissibleRing (withAdicTopology I)]
    (n : ℕ) :
    spfAdicCompletionι structureHom I n ≫ toSpfAdicSpf structureHom I =
      yoneda.map (powerStageToAdicStage structureHom I n) ≫
        colimit.ι
          (thickenings (withAdicTopology I)
            (structureHomCompletionAdic structureHom I) ⋙ yoneda)
          (evalWeakIdealAdic I n) :=
  sorry


/-- If `I` is finitely generated, the `I`-adic topology on the completion is an
adic ring topology. -/
theorem isAdicRing_withAdicTopology_of_fg (I : Ideal A) (hI : I.FG) :
    TopologicalRing.IsAdicRing (withAdicTopology I) :=
  sorry

/-- If `I` is finitely generated, the `I`-adic topology is weakly admissible, so
`spf` of the completion is defined. -/
theorem isWeaklyAdmissibleRing_withAdicTopology_of_fg (I : Ideal A) (hI : I.FG) :
    TopologicalRing.IsWeaklyAdmissibleRing (withAdicTopology I) :=
  sorry

/-- The comparison `X^∧_Z ⟶ Spf(A^∧)` when `I` is finitely generated. -/
def toSpfAdic_of_fg {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : I.FG) :
    spfAdicCompletion structureHom I ⟶
      @spf (withAdicTopology I) _ _
        (isWeaklyAdmissibleRing_withAdicTopology_of_fg I hI) _
        (structureHomCompletionAdic structureHom I) :=
  @toSpfAdicSpf _ _ _ structureHom I
    (isWeaklyAdmissibleRing_withAdicTopology_of_fg I hI)

/-- Restricting `toSpfAdic_of_fg` to the `n`th power stage recovers the stage
comparison followed by the adic `spf` cocone leg. -/
theorem toSpfAdic_of_fg_ι {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : I.FG) (n : ℕ) :
    spfAdicCompletionι structureHom I n ≫ toSpfAdic_of_fg structureHom I hI =
      yoneda.map (powerStageToAdicStage structureHom I n) ≫
        colimit.ι
          (thickenings (withAdicTopology I)
            (structureHomCompletionAdic structureHom I) ⋙ yoneda)
          (evalWeakIdealAdic I n) :=
  sorry

/-- If `I` is finitely generated, the extended ideal is finitely generated. -/
theorem evalIdealAdic_fg_of_fg (I : Ideal A) (hI : I.FG) :
    (evalIdealAdic I).FG :=
  sorry

/-- If `I` is finitely generated, the extended ideal is an ideal of definition
for the `I`-adic topology. -/
theorem evalIdealAdic_isIdealOfDefinition_of_fg (I : Ideal A) (hI : I.FG) :
    TopologicalRing.Ideal.IsIdealOfDefinition (evalIdealAdic I) :=
  sorry

end InverseLimitAndAdic

/-- An affine formal algebraic space is weakly adic when it is isomorphic to
`spf` of a weakly adic topological ring. -/
@[mk_iff]
class IsWeaklyAdic {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is a weakly adic ring and a structure morphism whose formal spectrum
  is isomorphic to `X`. -/
  exists_weaklyAdic :
    ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsWeaklyAdicRing B)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (σ : Spec (.of B) ⟶ S),
      Nonempty (X ≅ spf B σ)

namespace IsWeaklyAdic

/-- The formal spectrum of a weakly adic ring is a weakly adic affine formal
algebraic space. -/
instance instSpf (B : Type u) [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdicRing B] {S : Scheme.{u}}
    (σ : Spec (.of B) ⟶ S) :
    IsWeaklyAdic (spf B σ) :=
  sorry

/-- A weakly adic affine formal algebraic space is isomorphic to the formal
spectrum of a weakly adic ring. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsWeaklyAdic X] :
    ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsWeaklyAdicRing B)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (σ : Spec (.of B) ⟶ S),
      Nonempty (X ≅ spf B σ) :=
  sorry

/-- Weakly adic affine formal algebraic spaces are exactly functors isomorphic
to the formal spectrum of a weakly adic ring. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsWeaklyAdic X ↔
      ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
        (_ : TopologicalRing.IsWeaklyAdicRing B)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
        (σ : Spec (.of B) ⟶ S),
        Nonempty (X ≅ spf B σ) :=
  sorry

end IsWeaklyAdic

end AlgebraicGeometry.AffineFormalAlgebraicSpace
