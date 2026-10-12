/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace

/-!
# Canonical additive instances for sheaf-module categories

This historical support path checks the canonical instances supplied by Mathlib and ReasLib.  It
does not register parallel Chapter 20 instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TopCat
open TopologicalSpace

universe u

variable (X : TopCat.{u})

#synth Preadditive (X.Sheaf AddCommGrpCat.{u})
#synth HasZeroMorphisms (X.Sheaf AddCommGrpCat.{u})

variable (Y : AlgebraicGeometry.RingedSpace.{u})

#synth HasZeroMorphisms Y.Modules
