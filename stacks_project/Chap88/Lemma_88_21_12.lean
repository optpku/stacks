/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion
public import stacks_project.Chap88.Definition_88_20_1_Etale
public import stacks_project.Chap88.Definition_88_21_1
public import stacks_project.Chap88.Lemma_88_21_12_Affine

/-!
# Closed immersions that are rig-surjective

A closed immersion of locally Noetherian formal algebraic spaces is
rig-surjective if and only if every étale test map from an affine formal
algebraic space has base change corresponding to a surjection of adic
Noetherian rings whose kernel is killed by a power of an ideal of definition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace
  AffineFormalAlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- Lemma 88.21.12: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces. Assume that `X` and `Y` are locally Noetherian and
`f` is a closed immersion. Then `f` is rig-surjective if and only if for
every affine formal algebraic space `V` and every morphism `v : V ⟶ Y` which
is representable by algebraic spaces and étale, the morphism
`pullback.snd f v : X ×_Y V ⟶ V` corresponds to a surjective morphism of
adic Noetherian rings whose kernel `J` satisfies `I * J ^ n = ⊥` for some
ideal of definition `I` and some `n ≥ 1`. -/
@[stacks 0GD5]
theorem iff_etaleAffine_kernel {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] [LocallyOfFiniteType f] :
    RigSurjective f ↔
      ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
        (v : V ⟶ Y) [Etale v] [HasPullback f v]
        [IsFormalAlgebraicSpace (pullback f v)] [IsAffine (pullback f v)],
        KernelKilledByPowIdealOfDefinition (pullback.snd f v) :=
  sorry

/-- If every étale morphism from an affine formal algebraic space to `Y` has
base change `pullback.snd f v` corresponding to a surjection of adic
Noetherian rings whose kernel is killed by a power of an ideal of definition,
then the closed immersion `f` is rig-surjective. -/
theorem of_etaleAffine_kernel {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] [LocallyOfFiniteType f]
    (h : ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
      (v : V ⟶ Y) [Etale v] [HasPullback f v]
      [IsFormalAlgebraicSpace (pullback f v)] [IsAffine (pullback f v)],
      KernelKilledByPowIdealOfDefinition (pullback.snd f v)) :
    RigSurjective f :=
  sorry

/-- A rig-surjective closed immersion of locally Noetherian formal algebraic
spaces has the property that every étale morphism from an affine formal
algebraic space to `Y` has base change corresponding to a surjection of adic
Noetherian rings whose kernel is killed by a power of an ideal of
definition. -/
theorem etaleAffine_kernel {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] [LocallyOfFiniteType f] [RigSurjective f]
    {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
    (v : V ⟶ Y) [Etale v] [HasPullback f v]
    [IsFormalAlgebraicSpace (pullback f v)] [IsAffine (pullback f v)] :
    KernelKilledByPowIdealOfDefinition (pullback.snd f v) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
