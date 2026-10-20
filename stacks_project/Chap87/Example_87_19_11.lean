module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdealCompletion
import StacksCheckRecall

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_19_8
public import stacks_project.Chap87.Lemma_87_19_13_Functor

/-!
# Example 87.19.11

If `B` is weakly admissible and `A` is a `B`-algebra with no topology, the
weak-ideal completion `weakIdealCompletion B A` is weakly admissible, the
algebra map `B → (A)^∧` is taut, and `Spf((A)^∧) ⟶ Spf(B)` is representable
by algebraic spaces as in Lemma 87.19.8.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Example 87.19.11: The weak-ideal completion of an arbitrary algebra over a
weakly admissible ring induces a formal-spectrum morphism representable by
algebraic spaces, as a taut special case of Lemma 87.19.8. -/
@[stacks 0AN6] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.representableByAlgebraicSpaces_spfMap_weakIdealCompletion :
    ∀ {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
      [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
      (A : Type u) [CommRing A] [Algebra B A],
      AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
          (spfMap_weakIdealCompletion hB A)))

#check (TopologicalRing.weakIdealCompletion.eval_surjective :
  ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J),
    Function.Surjective (weakIdealCompletion.eval B A hJ))

#check (TopologicalRing.weakIdealCompletion.eval_ker_eq_closure :
  ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    [IsWeaklyAdmissibleRing B] {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J),
    RingHom.ker (weakIdealCompletion.eval B A hJ) =
      (J.map (algebraMap B (weakIdealCompletion B A))).closure)

#check (TopologicalRing.weakIdealCompletion.mem_eval_ker :
  ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    [IsWeaklyAdmissibleRing B] {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J)
    {x : weakIdealCompletion B A},
    x ∈ RingHom.ker (weakIdealCompletion.eval B A hJ) ↔
      x ∈ (J.map (algebraMap B (weakIdealCompletion B A))).closure)

#check (TopologicalRing.weakIdealCompletion.isWeakIdealOfDefinition_eval_ker :
  ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    [IsWeaklyAdmissibleRing B] {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J),
    Ideal.IsWeakIdealOfDefinition (RingHom.ker (weakIdealCompletion.eval B A hJ)))

#check (TopologicalRing.weakIdealCompletion.isOpen_eval_ker :
  ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    [IsWeaklyAdmissibleRing B] {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J),
    IsOpen (RingHom.ker (weakIdealCompletion.eval B A hJ) : Set (weakIdealCompletion B A)))

#check (TopologicalRing.instIsWeaklyAdmissibleRing_weakIdealCompletion :
  ∀ (B A : Type u) [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    [IsWeaklyAdmissibleRing B], IsWeaklyAdmissibleRing (weakIdealCompletion B A))

#check (TopologicalRing.weakIdealCompletion.isTaut_algebraMap :
  ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    [IsWeaklyAdmissibleRing B], (algebraMap B (weakIdealCompletion B A)).IsTaut)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.relativelyRepresentable_spfMap_weakIdealCompletion :
  ∀ {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (A : Type u) [CommRing A] [Algebra B A],
    yoneda.relativelyRepresentable
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hB A)))
