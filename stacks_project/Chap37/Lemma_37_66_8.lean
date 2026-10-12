/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.LocallyQuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.66.8: a separated locally quasi-finite morphism of schemes is
ind-quasi-affine. -/
@[stacks 0AP9] #check
  (AlgebraicGeometry.LocallyQuasiFinite.indQuasiAffineHom :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.LocallyQuasiFinite f]
      [AlgebraicGeometry.IsSeparated f],
      AlgebraicGeometry.IndQuasiAffineHom f)
