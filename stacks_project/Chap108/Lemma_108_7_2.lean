module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.«99_9_1_1_Functor»
public import stacks_project.Chap99.Proposition_99_9_4
public import stacks_project.Chap108.Lemma_108_5_2_Separated

/-!
# Lemma 108.7.2

The structure morphism of the Grothendieck Hilbert functor over `B` is
separated and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.7.2 (1): the structure morphism of `hilbert f` over `B` is
separated. -/
@[stacks 0DM7]
instance instIsSeparatedOver (f : X ⟶ B) [FinitePresentation f]
    [Separated f] :
    Quot.IsSeparatedOver (hilbert f) :=
  sorry

/-- Lemma 108.7.2 (2): the structure morphism of `hilbert f` over `B` is
locally of finite presentation. -/
@[stacks 0DM7]
theorem isLocallyOfFinitePresentationOver (f : X ⟶ B) [FinitePresentation f]
    [Separated f] :
    IsLocallyOfFinitePresentationOver (hilbert f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
