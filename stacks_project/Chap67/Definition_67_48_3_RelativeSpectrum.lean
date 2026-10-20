/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Affine
public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
import StacksCheckRecall

/-!
# Relative spectrum of a quasi-coherent algebra on an algebraic space

This is the source-facing facade for `definition-relative-spec`, Stacks tag
081W. The canonical relative spectrum has the original functor of base arrows
and descended algebra maps, an actual section-spectrum atlas and represented
diagonal, and its affine structural morphism. The universal algebra map and
hom correspondence express the affine/algebra correspondence of tag 081V.
The native inverse-image pushout construction supplies arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

#check AlgebraicSpace.relativeSpectrumPair
#check AlgebraicSpace.relativeSpectrumFunctor
#check AlgebraicSpace.relativeSpec
#check AlgebraicSpace.relativeSpecπ
#check AlgebraicSpace.relativeSpecπ_isAffine
#check AlgebraicSpace.relativeSpecπ_presheaf_affine
/- Definition 67.20.8: the relative spectrum corresponds to the supplied algebra. -/
@[stacks 081W] #check
  (AlgebraicSpace.relativeSpecUniversalAlgebraIso :
    {S : Scheme} → {X : AlgebraicSpace S} → (A : X.QcAlgebraUnder) →
      A.obj ≅ CategoryTheory.Under.mk (AlgebraicSpace.commStructureSheafMap (AlgebraicSpace.relativeSpecπ A)))
#check AlgebraicSpace.relativeSpecHomEquiv
#check AlgebraicSpace.relativeSpecBaseChange_isPullback
