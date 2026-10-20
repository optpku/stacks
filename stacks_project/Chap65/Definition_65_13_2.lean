/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 65.13.2 (1): an algebraic space `F` over a scheme `S` is separated over `S` if
the diagonal `diag F` is a closed immersion. -/
@[stacks 02X5] #check (AlgebraicGeometry.AlgebraicSpace.IsSeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Definition 65.13.2 (2): an algebraic space `F` over a scheme `S` is locally separated over `S`
if the diagonal `diag F` is an immersion. -/
@[stacks 02X5] #check (AlgebraicGeometry.AlgebraicSpace.IsLocallySeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Definition 65.13.2 (3): an algebraic space `F` over a scheme `S` is quasi-separated over `S` if
the diagonal `diag F` is quasi-compact. -/
@[stacks 02X5] #check (AlgebraicGeometry.AlgebraicSpace.IsQuasiSeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Definition 65.13.2 (4): an algebraic space `F` over a scheme `S` is Zariski locally
quasi-separated over `S` if it admits a Zariski covering by quasi-separated open subspaces. -/
@[stacks 02X5] #check (AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
