/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.«99_8_1_1_Functor»
public import stacks_project.Chap99.Proposition_99_8_4
public import stacks_project.Chap108.Lemma_108_5_2_Separated

/-!
# Lemma 108.5.2

The structure morphism of the Grothendieck Quot functor over `B` is separated,
and locally of finite presentation when the source module is of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.5.2 (1): the structure morphism of `quot f F` over `B` is
separated. -/
@[stacks 0DM3]
instance instIsSeparatedOver (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] :
    IsSeparatedOver (quot f F) :=
  sorry

/-- Lemma 108.5.2 (2): if `F` is of finite presentation, then the structure
morphism of `quot f F` over `B` is locally of finite presentation. -/
@[stacks 0DM3]
theorem isLocallyOfFinitePresentationOver (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    IsLocallyOfFinitePresentationOver (quot f F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
