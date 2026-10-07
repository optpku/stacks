module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalDivisor

namespace AlgebraicGeometry

universe u

open CategoryTheory

/- Lemma 31.32.4 (1): a blowup morphism is an isomorphism over the complement of the center. -/
@[stacks 02OS] #check
  (AlgebraicGeometry.IsBlowup.instIsIsoRestrictComplSupport :
    ∀ {X X' : Scheme.{u}} {I : X.IdealSheafData} {f : X' ⟶ X}
      [AlgebraicGeometry.IsBlowup f I],
      IsIso (f ∣_ ⟨(I.support : Set X)ᶜ, I.support.2.isOpen_compl⟩))

/- Lemma 31.32.4 (2): the inverse-image center of a blowup is an effective Cartier divisor. -/
@[stacks 02OS] #check
  (AlgebraicGeometry.IsBlowup.instIsEffectiveCartierDivisor :
    ∀ {X X' : Scheme.{u}} {I : X.IdealSheafData} {f : X' ⟶ X}
      [AlgebraicGeometry.IsBlowup f I],
      AlgebraicGeometry.IsEffectiveCartierDivisor (I.comap f).subschemeι)

/- Lemma 31.32.4 (3): the canonical map from the exceptional ideal sheaf to the first Rees
twist is an isomorphism. -/
@[stacks 02OS] #check
  (AlgebraicGeometry.Blowup.exceptionalIdealToTwistOne_isIso :
    ∀ {X : Scheme.{u}} {I : X.IdealSheafData} (π : AlgebraicGeometry.Blowup X I),
      IsIso π.reesPresentation.exceptionalIdealToTwistOne)

end AlgebraicGeometry
