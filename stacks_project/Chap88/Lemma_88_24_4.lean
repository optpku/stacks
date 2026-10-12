/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_24_4_Pullback
public import stacks_project.Chap88.Definition_88_24_1_Modification

/-!
# Base change of formal modifications of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace FormalModification

/-- Lemma 88.24.4: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S` which is a formal
modification. Then for any adic morphism `g : Z ⟶ Y` of locally Noetherian
formal algebraic spaces, i.e. `AlgebraicSpace.representableByAlgebraicSpaces g`
in the sense of Definition 87.23.2, the base change `X ×_Y Z ⟶ Z`, i.e.
`pullback.snd f g`, is a formal modification. -/
@[stacks 0GDN]
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [LocallyOfFiniteType f]
    [FormalModification f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    FormalModification (pullback.snd f g) :=
  sorry

/-- If `IsPullback fst snd f g`, `f` is a formal modification, and `g` is adic,
i.e. `AlgebraicSpace.representableByAlgebraicSpaces g`, then the base-change
leg `snd` is a formal modification. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [LocallyOfFiniteType f]
    [FormalModification f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    [LocallyOfFiniteType snd] :
    FormalModification snd :=
  sorry

end FormalModification

end AlgebraicGeometry.FormalAlgebraicSpace
