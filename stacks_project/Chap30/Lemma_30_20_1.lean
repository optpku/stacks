/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 30.20.1: let `A` be a Noetherian ring and `I ⊂ A` an ideal. If
`f : X ⟶ Spec A` is proper and `F` is coherent, then for every `p` the direct sum
`⨁ n : ℕ, H^p(X, I^n F)`, with its canonical Rees algebra action, is finite. -/
@[stacks 02O8] #check
  (AlgebraicGeometry.Scheme.Modules.IdealPowerCohomology.finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (I : Ideal A)
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (F : X.Modules) [F.IsCoherent]
      (p : ℕ),
      Module.Finite (reesAlgebra I)
        (AlgebraicGeometry.Scheme.Modules.IdealPowerCohomology.carrier I f F p))
