/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 50.3.1 (1): derived global sections of the relative de Rham complex of an affine
scheme morphism agree with the algebraic relative de Rham complex. -/
@[stacks 0FLW] #check
  (AlgebraicGeometry.Scheme.DeRham.affineDerivedGlobalSections_isomorphic :
    ∀ {R A : CommRingCat.{u}} (f : R ⟶ A),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DeRham.affineDerivedGlobalSections f)
        (AlgebraicGeometry.Scheme.DeRham.algebraicDerivedComplex f))

/- Lemma 50.3.1 (2): affine relative de Rham cohomology agrees degreewise with the
cohomology of the algebraic relative de Rham complex. -/
@[stacks 0FLW] #check
  (AlgebraicGeometry.Scheme.DeRham.affineCohomology_isomorphic :
    ∀ {R A : CommRingCat.{u}} (f : R ⟶ A) (i : ℤ),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DeRham.affineCohomology f i)
        (AlgebraicGeometry.Scheme.DeRham.algebraicCohomology f i))
