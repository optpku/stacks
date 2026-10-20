module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.ZariskiLocalFactorization

/-!
# Finite covers factoring Zariski locally through a stack morphism

A quasi-compact quasi-separated algebraic space admits, after a finite
surjective base change, a Zariski-local factoring of the inverse image of a
quasi-compact open through any surjective flat locally-of-finite-presentation
morphism of algebraic stacks onto that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For a quasi-compact, absolutely quasi-separated algebraic space and a
quasi-compact open subspace, every surjective flat locally-of-finite-presentation
morphism from an algebraic stack onto the open admits a finite surjective cover
of the ambient space whose restriction to the open factors Zariski locally
through the stack morphism. -/
@[stacks 0CQ6]
theorem exists_isFinite_surjective_zariskiLocallyFactorsThrough
    {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    (V : AlgebraicSpace.OpenSubspace Y) [AlgebraicSpace.IsQuasiCompact V.X]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ V.X.toGroupoids)
    [AlgebraicStack.Surjective f] [AlgebraicStack.Flat f]
    [AlgebraicStack.LocallyOfFinitePresentation f] :
    ∃ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
      AlgebraicSpace.IsFinite g ∧ AlgebraicSpace.Surjective g ∧
        zariskiLocallyFactorsThrough (AlgebraicSpace.restrictTo g V) f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
