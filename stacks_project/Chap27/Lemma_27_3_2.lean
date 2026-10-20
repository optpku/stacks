/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Sections

/-!
# Lemma 27.3.2 compatibility entry point

The affine-local section-ring and pullback-square API is owned by the neutral
quasi-coherent algebra infrastructure in ReasLib.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u

/- Lemma 27.3.2: restriction of a quasi-coherent algebra along nested affine opens. -/
@[stacks 01LN] #check
  (AlgebraicGeometry.Scheme.isPullback_specMap_qcAlgebraSectionRestrict :
    {S : Scheme.{u}} → (A : S.QcAlgebraUnder) → {U U' : S.Opens} →
      (hU : IsAffineOpen U) → (hU' : IsAffineOpen U') → (h : U ≤ U') →
        IsPullback
          (Spec.map (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict A h))
          (Spec.map (AlgebraicGeometry.Scheme.qcAlgebraStructureMap A U) ≫ hU.isoSpec.inv)
          (Spec.map (AlgebraicGeometry.Scheme.qcAlgebraStructureMap A U') ≫ hU'.isoSpec.inv)
          (S.homOfLE h))

#check
  (AlgebraicGeometry.Scheme.qcAlgebraSectionRing :
    {S : Scheme.{u}} → S.QcAlgebraUnder → S.Opens → CommRingCat)

#check
  (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict :
    {S : Scheme.{u}} → (A : S.QcAlgebraUnder) → {U U' : S.Opens} →
      U ≤ U' →
        CommRingCat.Hom
          (AlgebraicGeometry.Scheme.qcAlgebraSectionRing A U')
          (AlgebraicGeometry.Scheme.qcAlgebraSectionRing A U))

#check
  (AlgebraicGeometry.Scheme.qcAlgebraStructureMap :
    {S : Scheme.{u}} → (A : S.QcAlgebraUnder) → (U : S.Opens) →
      S.presheaf.obj (op U) ⟶ AlgebraicGeometry.Scheme.qcAlgebraSectionRing A U)

#check
  (AlgebraicGeometry.Scheme.specMap_qcAlgebraSectionRestrict_comp :
    {S : Scheme.{u}} → (A : S.QcAlgebraUnder) → {U U' U'' : S.Opens} →
      (hU : IsAffineOpen U) → (hU' : IsAffineOpen U') →
        (hU'' : IsAffineOpen U'') → (h : U ≤ U') → (h' : U' ≤ U'') →
          Spec.map (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict A h) ≫
              Spec.map (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict A h') =
            Spec.map
              (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict A (h.trans h')))
