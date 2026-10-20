/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 67.20.8: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent sheaf of `𝒪_X`-algebras `A`, the relative spectrum of `A` over `X`,
or simply the spectrum of `A` over `X`, is the affine morphism
`relativeSpecπ A : relativeSpec A ⟶ X` corresponding to `A` under the
equivalence of categories of Lemma 67.20.7. -/
@[stacks 081W] #check (AlgebraicGeometry.AlgebraicSpace.relativeSpecπ :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (A : AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder X),
    AlgebraicGeometry.AlgebraicSpace.relativeSpec A ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.instAffine_relativeSpecπ :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    Affine (relativeSpecπ A))

#check (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.ofQcAlgebra :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    AffineMorphismOver X)

#check (AlgebraicGeometry.AlgebraicSpace.relativeSpecUniversalAlgebraIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    A.obj ≅ Under.mk (commStructureSheafMap (relativeSpecπ A)))
