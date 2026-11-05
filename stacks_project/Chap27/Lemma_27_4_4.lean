/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Representability
import StacksCheckRecall

/-!
# Lemma 27.4.4 compatibility entry point

The canonical comparison from the explicitly glued relative spectrum to schemes
with specified representing points is owned by ReasLib.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 27.4.4: the constructed relative spectrum and a scheme with a specified
representing point are canonically isomorphic over the base. -/
@[stacks 01LV] #check
  (AlgebraicGeometry.Scheme.nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy :
    {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
      {Y : AlgebraicGeometry.Scheme.{u}} →
      (x : AlgebraicGeometry.Scheme.relativeSpectrumPair A Y) →
      (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentedBy x →
      (Over.mk (AlgebraicGeometry.Scheme.relativeSpectrumOver A).π ≅ Over.mk x.1))

/- The canonical comparison is determined by the constructed universal point. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpectrumComparison_point :
    {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
      {Y : AlgebraicGeometry.Scheme.{u}} →
      (x : AlgebraicGeometry.Scheme.relativeSpectrumPair A Y) →
      (hx : (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentedBy x) →
      AlgebraicGeometry.Scheme.relativeSpectrumPairPullbackMap A
          (AlgebraicGeometry.Scheme.relativeSpectrumComparison A x hx) x =
        (AlgebraicGeometry.Scheme.relativeSpectrumOver A).point)

#check
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

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctor.instIsRepresentable :
    {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
      (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentable)
