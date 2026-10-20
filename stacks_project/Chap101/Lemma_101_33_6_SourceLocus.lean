module

public import stacks_project.Chap100.Lemma_100_9_12_Opens
public import stacks_project.Chap100.Lemma_100_9_14_Union
public import stacks_project.Chap103.«103_15_1_1_Smooth»

/-!
# Smooth source locus of a morphism of algebraic stacks

The largest open substack of the source on which a morphism of algebraic stacks
is smooth, constructed as the union of all open substacks with that property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- The family of open substacks of `X` on which `f` is smooth. -/
def sourceLocusFamily {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    {U : OpenSubstack X // Smooth (U.ι ≫ f)} → OpenSubstack X :=
  Subtype.val

/-- The largest open substack of `X` on which `f` is smooth. -/
def sourceLocus {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    OpenSubstack X :=
  OpenSubstack.iUnion (sourceLocusFamily f)

/-- The restriction of `f` to its smooth source locus is smooth. -/
instance instSmooth_sourceLocus {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Smooth ((sourceLocus f).ι ≫ f) :=
  sorry

/-- Any open substack along which `f` is smooth is contained in the smooth
source locus on points. -/
theorem sourceLocus_maximal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (V : OpenSubstack X)
    (hV : Smooth (V.ι ≫ f)) :
    V.pointsSet ⊆ (sourceLocus f).pointsSet :=
  sorry

/-- The smooth source locus is the `iUnion` of the open substacks on which `f`
is smooth, the restriction of `f` is smooth, and every competing open is
contained in it on points. -/
theorem sourceLocus_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (sourceLocus f).objectProperty =
        OpenSubstack.objectProperty_iUnion (sourceLocusFamily f) ∧
      Smooth ((sourceLocus f).ι ≫ f) ∧
      ∀ V : OpenSubstack X,
        Smooth (V.ι ≫ f) → V.pointsSet ⊆ (sourceLocus f).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
