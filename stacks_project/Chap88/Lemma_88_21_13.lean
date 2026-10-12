/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion
public import stacks_project.Chap88.Definition_88_18_1
public import stacks_project.Chap88.Definition_88_20_1
public import stacks_project.Chap88.Definition_88_21_1
public import stacks_project.Chap88.Lemma_88_21_13_Affine

/-!
# Closed immersions that are rig-smooth and rig-surjective

A closed immersion of locally Noetherian formal algebraic spaces is
rig-smooth and rig-surjective if and only if it is rig-étale and
rig-surjective, if and only if every étale test map from an affine formal
algebraic space has base change corresponding to a surjection of adic
Noetherian rings whose kernel is killed by some ideal of definition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace
  AffineFormalAlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion

/-- Every étale morphism from an affine formal algebraic space to `Y` has
base change `pullback.snd f v` corresponding to a surjection of adic
Noetherian rings whose kernel is killed by some ideal of definition. -/
def etaleAffine_kernelKilled {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [ClosedImmersion f] : Prop :=
  ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
    (v : V ⟶ Y) [Etale v] [HasPullback f v]
    [IsFormalAlgebraicSpace (pullback f v)] [IsAffine (pullback f v)],
    KernelKilledByIdealOfDefinition (pullback.snd f v)

/-- `etaleAffine_kernelKilled f` means that every étale morphism from an
affine formal algebraic space to `Y` has base change corresponding to a
surjection of adic Noetherian rings whose kernel is killed by some ideal of
definition. -/
theorem etaleAffine_kernelKilled_iff {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    etaleAffine_kernelKilled f ↔
      ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
        (v : V ⟶ Y) [Etale v] [HasPullback f v]
        [IsFormalAlgebraicSpace (pullback f v)] [IsAffine (pullback f v)],
        KernelKilledByIdealOfDefinition (pullback.snd f v) :=
  sorry

/-- Lemma 88.21.13: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces. Assume that `X` and `Y` are locally Noetherian and
`f` is a closed immersion. The following are equivalent: `f` is rig-smooth
and rig-surjective; `f` is rig-étale and rig-surjective; for every affine
formal algebraic space `V` and every morphism `v : V ⟶ Y` which is
representable by algebraic spaces and étale, the morphism
`pullback.snd f v : X ×_Y V ⟶ V` corresponds to a surjective morphism of
adic Noetherian rings whose kernel `J` satisfies `I * J = ⊥` for some ideal
of definition `I`. -/
@[stacks 0GD6]
theorem tfae_rigSmooth_rigSurjective {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] [LocallyOfFiniteType f] :
    List.TFAE
      [RigSmooth f ∧ RigSurjective f, RigEtale f ∧ RigSurjective f,
        etaleAffine_kernelKilled f] :=
  sorry

/-- For a closed immersion of locally Noetherian formal algebraic spaces,
being rig-smooth and rig-surjective is equivalent to being rig-étale and
rig-surjective. -/
theorem rigSmooth_and_rigSurjective_iff_rigEtale {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] [LocallyOfFiniteType f] :
    RigSmooth f ∧ RigSurjective f ↔ RigEtale f ∧ RigSurjective f :=
  sorry

/-- For a closed immersion of locally Noetherian formal algebraic spaces,
being rig-étale and rig-surjective is equivalent to the étale-affine kernel
test with `I * J = ⊥`. -/
theorem rigEtale_and_rigSurjective_iff_kernel {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] [LocallyOfFiniteType f] :
    RigEtale f ∧ RigSurjective f ↔ etaleAffine_kernelKilled f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion
