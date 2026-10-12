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
public import stacks_project.Chap88.Lemma_88_20_9_Affine

/-!
# Closed immersions that are rig-smooth

A closed immersion of locally Noetherian formal algebraic spaces is
rig-smooth if and only if it is rig-étale, if and only if every étale test
map from an affine formal algebraic space has base change corresponding to a
surjection of adic Noetherian rings whose kernel cotangent is annihilated by
some ideal of definition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace
  AffineFormalAlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion

/-- Every étale morphism from an affine formal algebraic space to `Y` has
base change `pullback.snd f v` corresponding to a surjection of adic
Noetherian rings whose kernel cotangent is annihilated by some ideal of
definition. -/
def etaleAffine_kernelCotangent {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [ClosedImmersion f] : Prop :=
  ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
    (v : V ⟶ Y) [Etale v] [HasPullback f v]
    [IsFormalAlgebraicSpace (pullback f v)] [IsAffine (pullback f v)],
    KernelCotangentAnnihilatedByIdealOfDefinition (pullback.snd f v)

/-- `etaleAffine_kernelCotangent f` means that every étale morphism from an
affine formal algebraic space to `Y` has base change corresponding to a
surjection of adic Noetherian rings whose kernel cotangent is annihilated by
some ideal of definition. -/
theorem etaleAffine_kernelCotangent_iff {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    etaleAffine_kernelCotangent f ↔
      ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
        (v : V ⟶ Y) [Etale v] [HasPullback f v]
        [IsFormalAlgebraicSpace (pullback f v)] [IsAffine (pullback f v)],
        KernelCotangentAnnihilatedByIdealOfDefinition (pullback.snd f v) :=
  sorry

/-- Lemma 88.20.9: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces. Assume that `X` and `Y` are locally Noetherian and
`f` is a closed immersion. The following are equivalent: `f` is rig-smooth;
`f` is rig-étale; for every affine formal algebraic space `V` and every
morphism `v : V ⟶ Y` which is representable by algebraic spaces and étale,
the morphism `pullback.snd f v : X ×_Y V ⟶ V` corresponds to a surjective
morphism of adic Noetherian rings whose kernel `J` satisfies
`I • J.Cotangent = 0` for some ideal of definition `I`. -/
@[stacks 0GD4]
theorem tfae_rigSmooth {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    List.TFAE [RigSmooth f, RigEtale f, etaleAffine_kernelCotangent f] :=
  sorry

/-- For a closed immersion of locally Noetherian formal algebraic spaces,
rig-smoothness is equivalent to rig-étaleness. -/
theorem rigSmooth_iff_rigEtale {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    RigSmooth f ↔ RigEtale f :=
  sorry

/-- For a closed immersion of locally Noetherian formal algebraic spaces,
rig-étaleness is equivalent to the étale-affine kernel-cotangent test. -/
theorem rigEtale_iff_kernelCotangent {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    RigEtale f ↔ etaleAffine_kernelCotangent f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion
