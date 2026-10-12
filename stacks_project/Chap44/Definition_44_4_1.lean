/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (X T : Over S)

/- The relative Picard presheaf evaluates on `T` as the Picard group of `T ×ₛ X`. -/
#check (AlgebraicGeometry.RelativePicard.presheaf_obj X T :
  (AlgebraicGeometry.RelativePicard.presheaf X).obj (op T) =
    (T ⊗ X).left.PicardGroup)

/- Definition 44.4.1 (1): the Picard functor of `X ⟶ S` is the fppf sheafification of
the presheaf `T ↦ Pic(T ×ₛ X)`. -/
@[stacks 0B9L]
#check (AlgebraicGeometry.RelativePicard.functor_val X :
  (AlgebraicGeometry.RelativePicard.functor X).obj =
    (Scheme.fppfTopology.over S).sheafify
      (AlgebraicGeometry.RelativePicard.presheaf X))

variable [(AlgebraicGeometry.RelativePicard.functor X).obj.IsRepresentable]

/- Definition 44.4.1 (2): when the relative Picard functor is representable,
`RelativePicard.scheme X` is a chosen representing `S`-scheme. -/
@[stacks 0B9L]
#check (AlgebraicGeometry.RelativePicard.schemeRepresentation X :
  (AlgebraicGeometry.RelativePicard.functor X).obj.RepresentableBy
    (AlgebraicGeometry.RelativePicard.scheme X))

end AlgebraicGeometry
