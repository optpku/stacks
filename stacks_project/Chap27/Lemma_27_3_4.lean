/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Realization
import StacksCheckRecall

/-!
# Lemma 27.3.4 compatibility entry point

The relative-spectrum realization construction and its equipped uniqueness API
are owned by ReasLib.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- The affine-basis gluing datum for the spectra of the section rings of a
quasi-coherent algebra. -/
#check (AlgebraicGeometry.Scheme.relativeSpectrumGluingData :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder),
    AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, u} S)

/- The reusable predicate records the affine-local spectrum identifications and their
compatibility with restriction. -/
#check (AlgebraicGeometry.Scheme.realizesRelativeSpectrum :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder) {X : Scheme.{u}} (π : X ⟶ S), Prop)

/- An equipped realization records the global scheme, its structural morphism, and
compatible affine-local spectrum identifications. -/
#check (AlgebraicGeometry.Scheme.RelativeSpectrumRealization :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder), Type (u + 1))

/- Compatible isomorphisms of equipped realizations preserve both the structural
morphism and the chosen affine-local identifications. -/
#check (AlgebraicGeometry.Scheme.RelativeSpectrumRealizationIso :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder)
    (R R' : AlgebraicGeometry.Scheme.RelativeSpectrumRealization A), Type u)

/- Forgetting the equipped local identifications gives the underlying realization
predicate. -/
#check (AlgebraicGeometry.Scheme.RelativeSpectrumRealization.realizes :
  ∀ {S : Scheme.{u}} {A : S.QcAlgebraUnder}
    (R : AlgebraicGeometry.Scheme.RelativeSpectrumRealization A),
      AlgebraicGeometry.Scheme.realizesRelativeSpectrum A R.toBase)

/- Every quasi-coherent algebra has an equipped relative-spectrum realization. -/
#check (AlgebraicGeometry.Scheme.RelativeSpectrumRealization.nonempty :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder),
    Nonempty (AlgebraicGeometry.Scheme.RelativeSpectrumRealization A))

/- Two equipped realizations have a unique compatible isomorphism. -/
#check (AlgebraicGeometry.Scheme.RelativeSpectrumRealization.existsUniqueIso :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder)
    (R R' : AlgebraicGeometry.Scheme.RelativeSpectrumRealization A),
      ∃ e : AlgebraicGeometry.Scheme.RelativeSpectrumRealizationIso A R R',
        ∀ e' : AlgebraicGeometry.Scheme.RelativeSpectrumRealizationIso A R R', e' = e)

/- Lemma 27.3.4

An equipped relative-spectrum realization exists and is uniquely compatibly
isomorphic to every other equipped realization. -/
@[stacks 01LP] #check (AlgebraicGeometry.Scheme.exists_relativeSpectrumRealization_uniqueUpToUniqueIso :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder),
    ∃ R : AlgebraicGeometry.Scheme.RelativeSpectrumRealization A,
      ∀ R' : AlgebraicGeometry.Scheme.RelativeSpectrumRealization A,
        ∃ e : AlgebraicGeometry.Scheme.RelativeSpectrumRealizationIso A R R',
          ∀ e' : AlgebraicGeometry.Scheme.RelativeSpectrumRealizationIso A R R', e' = e)

/- Forgetting the equipped data yields a scheme over the base with the affine-local
relative-spectrum realization property. -/
#check (AlgebraicGeometry.Scheme.exists_scheme_over_realizingRelativeSpectrum :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder),
    ∃ (X : Scheme.{u}) (π : X ⟶ S),
      AlgebraicGeometry.Scheme.realizesRelativeSpectrum A π)

/- Every morphism satisfying the reusable relative-spectrum realization predicate is affine. -/
#check (AlgebraicGeometry.Scheme.isAffineHom_of_realizesRelativeSpectrum :
  ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder) {X : Scheme.{u}} {π : X ⟶ S},
    AlgebraicGeometry.Scheme.realizesRelativeSpectrum A π → AlgebraicGeometry.IsAffineHom π)
