/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BivariantClass.ZeroSchemeGysin

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 82.26.6. The refined Gysin maps associated to a section of an
invertible module on a good algebraic space form a bivariant class of degree one. -/
@[stacks 0ERP] #check (AlgebraicGeometry.AlgebraicSpace.BivariantClass.gysin :
    {S : Scheme.{u}} → {B X : AlgebraicSpace S} →
    [UniversallyCatenary B] → [IsQuasiSeparated B] →
    (δ : Points B → ℤ) → [IsDimensionFunction δ] →
    (pX : X ⟶ B) → [QuasiSeparated pX] → [LocallyOfFiniteType pX] →
    (L : X.Modules) → [isInvertibleObject L] → (s : L.sections) →
    BivariantClass δ pX (zeroSchemeι L s) 1)

