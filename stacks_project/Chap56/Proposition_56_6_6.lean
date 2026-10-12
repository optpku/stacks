/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Reconstruction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Proposition 56.6.6: for quasi-compact and quasi-separated schemes `X` and `Y`,
an equivalence `F : Scheme.QCoh X ⥤ Scheme.QCoh Y` is naturally isomorphic to
pullback along a scheme isomorphism `f : Y ≅ X` followed by tensoring with an
invertible quasi-coherent `O_Y`-module `L`. -/
@[stacks 0GPJ] #check
  (AlgebraicGeometry.Scheme.QCoh.equivalence_pullback_tensor_invertible :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [F.IsEquivalence],
    ∃ (f : Y ≅ X) (L : Scheme.QCoh Y),
      Scheme.Modules.Invertible L.obj ∧
        Nonempty (F ≅ Scheme.QCoh.pullback f.hom ⋙ Scheme.QCoh.tensorRight L))
