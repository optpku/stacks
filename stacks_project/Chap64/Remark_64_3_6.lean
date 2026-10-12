/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.GeometricBaseChange
import StacksCheckRecall

/-!
# Absolute Frobenius versus base change of geometric Frobenius
-/

open AlgebraicGeometry CategoryTheory Scheme
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.SchemeOverField.geometricFrobenius_eq_absoluteFrobeniusPow :
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)
    (X : SchemeOverField k),
    SchemeOverField.geometricFrobenius p f X =
      Hom.absoluteFrobeniusPowSource (p := p) X.hom f)

/- Remark 64.3.6. Over the original finite field `k`, geometric Frobenius is
definitionally the absolute Frobenius iterate, also for an étale object packaged
as `Over.mk (U.hom ≫ X.hom)`. After base change to `AlgebraicClosure k`, however,
the absolute iterate need not equal the base-changed geometric Frobenius over
`k`; they already differ for `Spec k`. The absolute iterate over the algebraic
closure is not an intrinsic finite-field geometric Frobenius there. -/
@[stacks 03SS] #check (AlgebraicGeometry.SchemeOverField.baseChange_ne_absoluteFrobeniusPow :
  ∀ {k : Type u} [Field k] [Fintype k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)
    (hcard : Fintype.card k = p ^ f) [Algebra k (AlgebraicClosure k)],
    SchemeOverField.geometricFrobenius p f (FieldExtension.Over.baseChange k (AlgebraicClosure k)
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) ≠
      ((FieldExtension.Over.functor k (AlgebraicClosure k)).map
        (SchemeOverField.geometricFrobeniusOver p f hcard
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).left)
