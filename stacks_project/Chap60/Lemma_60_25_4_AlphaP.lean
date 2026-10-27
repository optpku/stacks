/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AlphaP

open AlgebraicGeometry CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (c : R)

/- The affine root-adjunction model and its target-local cover API. -/
#check (AlgebraicGeometry.adjoinRootAlphaPHom p R c :
  Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))) ⟶ Spec (.of R))
