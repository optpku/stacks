/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locus.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.16.6 (1): under the stated relative finite-presentation, flatness, and
finite-type hypotheses, the locus where `f` is flat at a point is open in `X`. -/
@[stacks 05VK]
#check (AlgebraicGeometry.Scheme.Hom.isOpen_flatAt :
  ∀ {S : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [Flat X.hom] [LocallyOfFiniteType Y.hom],
      IsOpen {x : X.left | Scheme.Hom.flatAt f.left x})

/- Lemma 37.16.6 (2): the pointwise flatness locus of `f` commutes with arbitrary
base change `s : S' ⟶ S`. -/
@[stacks 05VK]
#check (AlgebraicGeometry.Scheme.Hom.flatAt_baseChange_eq_preimage :
  ∀ {S S' : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [Flat X.hom] [LocallyOfFiniteType Y.hom]
    (s : S' ⟶ S),
      {x' : ((Over.pullback s).obj X).left |
          Scheme.Hom.flatAt ((Over.pullback s).map f).left x'} =
        (pullback.fst X.hom s).base ⁻¹' {x : X.left | Scheme.Hom.flatAt f.left x})

end AlgebraicGeometry.Scheme.Hom
