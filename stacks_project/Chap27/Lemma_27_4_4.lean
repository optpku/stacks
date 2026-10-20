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

The comparison between affine-local realizations and representing schemes is
owned by ReasLib.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 27.4.4: a realization and a scheme representing the relative-spectrum functor are
isomorphic over the base. -/
@[stacks 01LV] #check
  (AlgebraicGeometry.Scheme.nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy :
    {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
      {X Y : AlgebraicGeometry.Scheme.{u}} → {πX : X ⟶ S} →
      AlgebraicGeometry.Scheme.realizesRelativeSpectrum A πX →
      (x : AlgebraicGeometry.Scheme.relativeSpectrumPair A Y) →
      (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentedBy x →
      (Over.mk πX ≅ Over.mk x.1))

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
