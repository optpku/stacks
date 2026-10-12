/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Embedding
import StacksCheckRecall

/-!
Lemma 15.66.6 (0G8Y): a pseudo-coherent derived module admits, in every degree, a morphism to a
single finitely presented module which is injective on that degree of homology.  The reusable
owner also exports the differential-cokernel map used by later projective- and Tor-amplitude
arguments.

@stack 0G8Y
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

/- Lemma 15.66.6 (0G8Y), in its canonical pseudo-coherent-object namespace. -/
@[stacks 0G8Y]
#check fun {R : Type u} [Ring R] {K : DerivedCategory (ModuleCat R)}
    (hK : K.IsPseudoCoherent) (i : ℤ) ↦
  (DerivedCategory.IsPseudoCoherent.exists_finitelyPresented_single_mono hK i :
    ∃ (M : ModuleCat R) (_ : Module.FinitePresentation R M)
      (α : K ⟶ (DerivedCategory.singleFunctor (ModuleCat R) i).obj M),
      Mono (DerivedCategory.homologyToSingle (R := R) i α))

#check @CategoryTheory.to_single_of_differential_cokernel
#check @CategoryTheory.homologyMap_to_single_of_differential_cokernel_mono
#check @CategoryTheory.homologyToSingle_Q_map_to_single_of_differential_cokernel_mono
#check @CategoryTheory.mono_homologyToSingle_precompose_iso
