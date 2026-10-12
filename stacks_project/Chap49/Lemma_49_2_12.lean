/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Homology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.ModuleCat.UpperShriek

noncomputable section

universe u

/- Lemma 49.2.12 -/
@[stacks 0C0I]
#check (Algebra.RelativeDualizingModule.isomorphicHomologyZero :
    ∀ (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (p : Presentation (algebraMap A B)),
    IsIsomorphic (Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} B) 0).obj
        (p.functor.obj (ModuleCat.single0 (ModuleCat.of A A)))))
