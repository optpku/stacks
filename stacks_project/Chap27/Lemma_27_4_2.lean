/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Representability

/-!
# Lemma 27.4.2 compatibility entry point

Affine-base representability of the relative-spectrum functor is neutral
infrastructure owned by ReasLib.
-/

@[expose] public section

universe u

/- Lemma 27.4.2: affine-base representability of the relative-spectrum functor. -/
@[stacks 01LT] #check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctor_isRepresentedBySpecGlobalSections :
    {S : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsAffine S] →
      (A : S.QcAlgebraUnder) →
        ∃ x : (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).obj
            (Opposite.op
              (AlgebraicGeometry.Spec (AlgebraicGeometry.Scheme.qcAlgebraSectionRing A ⊤))),
          (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentedBy x)

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctor.instIsRepresentableOfIsAffine :
    {S : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsAffine S] →
      (A : S.QcAlgebraUnder) →
        (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentable)
