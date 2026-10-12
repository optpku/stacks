/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

/-- The canonical homothety `𝟙_ (ModuleDerived X) ⟶ (ihom C.complex).obj C.complex`
associated to a relative dualizing complex. -/
def homothety {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f] [MonoidalCategory (ModuleDerived X)]
    (C : RelativeDualizingComplex f) (H : MonoidalClosed (ModuleDerived X)) :
    𝟙_ (ModuleDerived X) ⟶
      (@ihom (ModuleDerived X) _ _ C.complex (H.closed C.complex)).obj C.complex :=
  @MonoidalClosed.curry' (ModuleDerived X) _ _ C.complex C.complex
    (H.closed C.complex) (𝟙 C.complex)

/-- Lemma 86.9.2 (1): for a proper, flat, finitely presented morphism of algebraic spaces,
the canonical homothety of any relative dualizing complex is an isomorphism. -/
@[stacks 0E5Y]
theorem homothety_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f] [MonoidalCategory (ModuleDerived X)]
    (C : RelativeDualizingComplex f) (H : MonoidalClosed (ModuleDerived X)) :
    IsIso (homothety C H) :=
  sorry

/-- Lemma 86.9.2 (2): for a proper, flat, finitely presented morphism of algebraic spaces,
the derived pushforward of any relative dualizing complex has vanishing cohomology sheaves
in every positive degree. -/
@[stacks 0E5Y]
theorem pushforward_cohomology_isZero_of_pos {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] [Flat f] [FinitePresentation f]
    (C : RelativeDualizingComplex f) (i : ℤ) (hi : 0 < i) :
    IsZero (cohomologySheaf ((moduleDerivedPushforward f).obj C.complex) i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
