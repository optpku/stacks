module

public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.MorphismProperty
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap70.Lemma_70_5_1_Points

/-!
# Zariski precoverage on algebraic spaces

The Zariski covering families of algebraic spaces over a scheme `S` are the
jointly surjective families of open immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The precoverage of jointly surjective families of morphisms of algebraic
spaces over `S`, measured on points. -/
def jointlySurjectivePrecoverage (S : Scheme.{u}) : Precoverage (AlgebraicSpace S) :=
  Types.jointlySurjectivePrecoverage.comap pointsFunctor

/-- The Zariski precoverage on algebraic spaces over `S`: jointly surjective
families of open immersions. -/
def zariskiPrecoverage (S : Scheme.{u}) : Precoverage (AlgebraicSpace S) :=
  jointlySurjectivePrecoverage S ⊓
    MorphismProperty.precoverage
      fun {X Y : AlgebraicSpace S} (f : X ⟶ Y) ↦ IsOpenImmersion f

/-- A displayed family is jointly surjective on points if and only if the images
of `Points.map` cover the target. -/
theorem ofArrows_mem_jointlySurjectivePrecoverage_iff {S : Scheme.{u}}
    {T : AlgebraicSpace S} {I : Type v} (X : I → AlgebraicSpace S)
    (f : ∀ i, X i ⟶ T) :
    Presieve.ofArrows X f ∈ jointlySurjectivePrecoverage S T ↔
      (⋃ i, Set.range (Points.map (f i))) = Set.univ :=
  sorry

/-- A displayed family is a Zariski covering if and only if each morphism is an
open immersion and the images of `Points.map` cover the target. -/
theorem ofArrows_mem_zariskiPrecoverage_iff {S : Scheme.{u}}
    {T : AlgebraicSpace S} {I : Type v} (X : I → AlgebraicSpace S)
    (f : ∀ i, X i ⟶ T) :
    Presieve.ofArrows X f ∈ zariskiPrecoverage S T ↔
      (∀ i, IsOpenImmersion (f i)) ∧
        (⋃ i, Set.range (Points.map (f i))) = Set.univ :=
  sorry

/-- A singleton family is a Zariski covering if and only if the morphism is an
open immersion that is surjective on points. -/
theorem singleton_mem_zariskiPrecoverage_iff {S : Scheme.{u}}
    {X T : AlgebraicSpace S} (f : X ⟶ T) :
    Presieve.singleton f ∈ zariskiPrecoverage S T ↔
      IsOpenImmersion f ∧ Function.Surjective (Points.map f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
