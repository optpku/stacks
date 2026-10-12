/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.IdealPower
public import ReasLib.RingTheory.Sequence.Koszul.WeakProregular
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape Opposite

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {r : ℕ} (f : Fin r → R)

/- Remark 24.35.5 (1) (tag 0H1E): in the chain-complex model, negative cohomology in the
source is positive homology. This source-shaped form chooses one later transition which kills
all positive homology degrees simultaneously. -/
@[stacks 0H1E "simultaneous transition form of weak proregularity"]
#check (KoszulComplex.IsWeaklyProregular.AtOnce f : Prop)

/- Finite Koszul amplitude identifies the source-shaped condition with the canonical
homologywise pro-zero property. -/
#check
  (KoszulComplex.isWeaklyProregular_iff_atOnce f :
    KoszulComplex.IsWeaklyProregular f ↔
      KoszulComplex.IsWeaklyProregular.AtOnce f)

/- Its fine-grained API exposes the eventual-zero condition degree by degree. -/
#check
  (KoszulComplex.isWeaklyProregular_iff f :
    KoszulComplex.IsWeaklyProregular f ↔
      ∀ p : ℕ, 0 < p →
        PreorderInverseSystem.Transition.EventuallyZero
          (KoszulComplex.powerSystem f ⋙
            HomologicalComplex.homologyFunctor (ModuleCat R) (down ℕ) p))

end


section Comparison

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

/- Remark 24.35.5 (2), available concrete input: the quotient system is defined without a
Noetherian hypothesis. The weak-proregular equivalence with its `QC` category still requires
the quotient-tower QC functor and canonical derived-completion comparison. -/
#check
  (idealPowerQuotientRingSystem I : ℕᵒᵖ ⥤ CommRingCat.{u})

end Comparison
