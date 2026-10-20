module

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.11.2 (1): an affine morphism is separated. -/
@[stacks 01S7] #check
  (@AlgebraicGeometry.IsSeparated.of_isAffineHom :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f], IsSeparated f)

/- Lemma 29.11.2 (2): an affine morphism is quasi-compact. -/
@[stacks 01S7] #check
  (@AlgebraicGeometry.instQuasiCompactOfIsAffineHom :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f], QuasiCompact f)
