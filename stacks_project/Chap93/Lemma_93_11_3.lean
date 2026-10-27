/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.TangentExt

/-! # Infinitesimal automorphisms and tangent space of algebraic-space deformations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

/-- The `k`-derivations of `𝒪_X` into itself, relative to the residue structure morphism. -/
abbrev FlatAlgebraicSpaceCat.derivations :=
  AlgebraicGeometry.AlgebraicSpace.Hom.derivations
    (FlatAlgebraicSpaceCat.ofResidue Λ k X).structureHom
    (SheafOfModules.unit (structureSheaf (FlatAlgebraicSpaceCat.ofResidue Λ k X).space))

/- Lemma 93.11.3 (1). Infinitesimal automorphisms identify with Ext⁰ of the naive
cotangent complex with structure-module coefficients. -/
@[stacks 0E41] #check
  (FlatAlgebraicSpaceCat.infToExtZero_bijective Λ k X :
    Function.Bijective (FlatAlgebraicSpaceCat.infToExtZero Λ k X))

/- Lemma 93.11.3 (2). Ext⁰ of the naive cotangent complex identifies with morphisms
from the sheaf of differentials, in the canonical Hom → Ext⁰ orientation. -/
@[stacks 0E41] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.homToExtZero_bijective
      (FlatAlgebraicSpaceCat.ofResidue Λ k X).structureHom
      (G := SheafOfModules.unit (structureSheaf (FlatAlgebraicSpaceCat.ofResidue Λ k X).space)) :
    Function.Bijective
      (AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.homToExtZero
        (FlatAlgebraicSpaceCat.ofResidue Λ k X).structureHom :
        (Ω[(FlatAlgebraicSpaceCat.ofResidue Λ k X).structureHom] ⟶
          SheafOfModules.unit (structureSheaf (FlatAlgebraicSpaceCat.ofResidue Λ k X).space)) →
        FlatAlgebraicSpaceCat.extZero Λ k X))

/- Lemma 93.11.3 (3). Morphisms from the sheaf of differentials identify with
relative derivations of the actual residue structure morphism. -/
@[stacks 0E41] #check
  (SheafOfModules.RingedSite.RelativeDifferentials.homEquiv
      (AlgebraicGeometry.AlgebraicSpace.commInverseImageStructureSheafMap
        (FlatAlgebraicSpaceCat.ofResidue Λ k X).structureHom)
      (SheafOfModules.unit (structureSheaf (FlatAlgebraicSpaceCat.ofResidue Λ k X).space)) :
    (Ω[(FlatAlgebraicSpaceCat.ofResidue Λ k X).structureHom] ⟶
      SheafOfModules.unit (structureSheaf (FlatAlgebraicSpaceCat.ofResidue Λ k X).space)) ≃
    AlgebraicGeometry.AlgebraicSpace.Hom.derivations
      (FlatAlgebraicSpaceCat.ofResidue Λ k X).structureHom
      (SheafOfModules.unit (structureSheaf (FlatAlgebraicSpaceCat.ofResidue Λ k X).space)))

/- Lemma 93.11.3 (4). Tangent classes identify with Ext¹ of the naive cotangent
complex with structure-module coefficients. -/
@[stacks 0E41] #check
  (FlatAlgebraicSpaceCat.ofExtOne_bijective Λ k X :
    Function.Bijective (FlatAlgebraicSpaceCat.ofExtOne Λ k X))
