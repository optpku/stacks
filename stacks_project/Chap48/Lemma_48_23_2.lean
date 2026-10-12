/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.SingleCohenMacaulay
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived

universe u

/- Lemma 48.23.2: A locally Noetherian scheme admitting a coherent sheaf whose
degree-zero complex is dualizing is Cohen-Macaulay. -/
@[stacks 0AWU] #check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.cohenMacaulayOfSingle :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (ωX : X.Modules) [ωX.IsCoherent],
      AlgebraicGeometry.Scheme.IsDualizingComplex
        ((DerivedCategory.singleFunctor X.Modules 0).obj ωX) →
        Scheme.CohenMacaulay X)
