module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Reduced
import StacksCheckRecall

/-!
# Reducedness of relative normalizations of algebraic spaces
-/

open CategoryTheory

universe u

/- Lemma 67.48.6: let `S` be a scheme, and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. If `X` is reduced, then the
relative normalization `normalization f` of `Y` in `X` is reduced.

In Stacks language, `f : Y ⟶ X` and `X'` are Lean `f : X ⟶ Y` and
`Hom.normalization f`, and reducedness of `Y` is `[IsReduced X]`. -/
@[stacks 0AYF] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isReduced_normalization :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
      [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f]
      [AlgebraicGeometry.AlgebraicSpace.IsReduced X],
      AlgebraicGeometry.AlgebraicSpace.IsReduced
        (AlgebraicGeometry.AlgebraicSpace.Hom.normalization f))
