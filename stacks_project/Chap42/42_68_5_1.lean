/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Module.FiniteLength.Determinant.Functor

open CategoryTheory

universe u v

variable (R : Type u) [CommRing R] [IsLocalRing R]

/- 42.68.5.1: The determinant assignment is a functor from finite-length `R`-modules and
their isomorphisms to one-dimensional vector spaces over the residue field and their
isomorphisms. -/
@[stacks 05M7] #check
  (Module.FiniteLengthDeterminant.functor R :
    Module.FiniteLengthDeterminant.ModuleCore.{u, v} R ⥤
      Module.FiniteLengthDeterminant.LineCore.{u, max u v} (IsLocalRing.ResidueField R))
