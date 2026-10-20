/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.StrictHenselization
import StacksCheckRecall

/-!
# Strict henselization of deformations of rings
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 93.8.9
In Example 93.8.1 let P be a k-algebra. Assume P is a local ring and let Psh
be a strict henselization of P. There is a natural functor of deformation
categories Def_P ⥤ Def_{Psh}. -/
@[stacks 0DYU]
#check (FlatAlgebraCat.exists_strictHenselizationFunctor :
  ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (P : Type u) [CommRing P] [Algebra k P]
    (Psh : Type u) [CommRing Psh] [Algebra k Psh] [Algebra P Psh]
    [IsLocalRing P] [IsScalarTower k P Psh] [IsStrictHenselizationOf P Psh],
    ∃ F : FlatAlgebraCat.deformationCategory Λ k P ⥤
        FlatAlgebraCat.deformationCategory Λ k Psh,
      FlatAlgebraCat.IsStrictHenselizationFunctor Λ k P Psh F)
