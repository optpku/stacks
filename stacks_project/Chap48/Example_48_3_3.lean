/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap48.Example_48_3_2
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.Counterexample
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedCoextension

/- Example 48.3.3: for a field `k`, the degree-zero cohomology of
`RHom_k(k[X], k[0])`, viewed as a `k[X]`-module via derived coextension of scalars,
is not finite. Thus the right adjoint to affine derived pushforward need not preserve
coherent cohomology. -/
@[stacks 0A9G] #check (CategoryTheory.ModuleCat.DerivedCoextension.polynomialHomologyNotFinite :
  ∀ (k : Type u) [Field k],
    ¬ Module.Finite (Polynomial k)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} (Polynomial k)) 0).obj
        ((derivedCoextensionOfScalars (algebraMap k (Polynomial k))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u, u} k) 0).obj
            (ModuleCat.of k k)))))

end CategoryTheory.ModuleCat.DerivedCoextension
