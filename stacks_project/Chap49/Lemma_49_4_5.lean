/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open Algebra.RelativeDualizingModule
open Algebra.RelativeDualizingModule.TraceElement

universe u

/- Lemma 49.4.5: a section of the relative dualizing module is a trace element if
it is a trace element after localization at each member of a finite family generating
the unit ideal. -/
@[stacks 0BTA]
#check (Algebra.RelativeDualizingModule.TraceElement.of_localizationAway_unitIdeal :
    ∀ (A B' B : Type u)
      [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
      [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (m : ℕ) (g : Fin m → B) (hunit : Ideal.span (Set.range g) = ⊤)
      (τ : of A B' B h_quasiFinite h_open),
      (∀ i, IsUniversal A B' (Localization.Away (g i))
        (quasiFiniteAwayTarget A B h_quasiFinite (g i))
        (openAwayTarget B' B h_open (g i))
        ((awayTargetIso A B' B h_quasiFinite h_open (g i)).hom
          (LocalizedModule.mk τ 1))) →
      IsUniversal A B' B h_quasiFinite h_open τ)
