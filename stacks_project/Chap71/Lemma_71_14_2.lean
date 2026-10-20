module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.SchemeComparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 71.14.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `L` be an invertible `𝒪_X`-module. Assume `Y` is
a scheme. Then `L` is ample on `X/Y` in the sense of Definition 71.14.1 if and
only if `X` is a scheme and `L` is ample on `X/Y` in the sense of Morphisms,
Definition 29.37.1. -/
@[stacks 0D32] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.iff_schemeRelativelyAmple :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
      [CategoryTheory.MonoidalCategory.isInvertibleObject L]
      [AlgebraicGeometry.AlgebraicSpace.IsScheme Y],
      AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L ↔
        AlgebraicGeometry.AlgebraicSpace.IsScheme X ∧
          ∀ {U V : CategoryTheory.Over S}
            (eX : X ≅ AlgebraicGeometry.AlgebraicSpace.ofOver U)
            (eY : Y ≅ AlgebraicGeometry.AlgebraicSpace.ofOver V),
            AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.schemeRelativelyAmple
              eX eY f L)
