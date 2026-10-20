/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Lemma_67_20_7_AffineOver

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Over

/-!
# Affine relative spectrum of a quasi-coherent algebra

The historical imports and typed checks expose the shared affine relative-spectrum
API to downstream consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.instAffine_relativeSpecπ :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    Affine (relativeSpecπ A))

#check (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.ofQcAlgebra :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    AffineMorphismOver X)

#check (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.ofQcAlgebra_obj :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    (AffineMorphismOver.ofQcAlgebra A).obj = Over.mk (relativeSpecπ A))

#check (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.ofQcAlgebra_hom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    (AffineMorphismOver.ofQcAlgebra A).obj.hom = relativeSpecπ A)

#check (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.ofQcAlgebra_left :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    (AffineMorphismOver.ofQcAlgebra A).obj.left = relativeSpec A)

#check (AlgebraicGeometry.AlgebraicSpace.relativeSpecUniversalAlgebraIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    A.obj ≅ Under.mk (commStructureSheafMap (relativeSpecπ A)))

#check (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.ofQcAlgebra_unique :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (Y : AffineMorphismOver X),
    Nonempty (Under.mk (commStructureSheafMap Y.obj.hom) ≅ A.obj) →
      Nonempty (Y ≅ AffineMorphismOver.ofQcAlgebra A))
