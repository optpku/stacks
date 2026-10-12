/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Nerve.SplitEpi.Homotopy
import StacksCheckRecall

@[expose] public section

/-!
@stack 019P

# Source-facing bridge for Lemma 14.26.9

The contraction of the Čech nerve of a split epimorphism is owned by ReasLib and is constructed
from mathlib's canonical extra degeneracy.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : Y ⟶ X)
variable [HasPullbacks C]
variable (s : X ⟶ Y) (hs : s ≫ f = 𝟙 X)

/- Lemma 14.26.9: factorwise, the section-induced Čech-nerve endomorphism composes each
wide-pullback projection with `f ≫ s`. -/
@[stacks 019P "Lemma 14.26.9 (factorwise formula)"]
#check fun (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) ↦
  (SplitEpi.cechNerve.sectionEndomorphism.map.app_π
      (f := f) (SplitEpi.mk s hs) n i :
    (SplitEpi.cechNerve.sectionEndomorphism.map
        (f := f) (SplitEpi.mk s hs)).app n ≫
        Arrow.cechNerve.π (Arrow.mk f) n i =
      Arrow.cechNerve.π (Arrow.mk f) n i ≫ f ≫ s)

/- Lemma 14.26.9 (1): the Čech-nerve endomorphism induced by `f ≫ s` is simplicially homotopic
to the identity. -/
@[stacks 019P "Lemma 14.26.9 (1)"]
#check (SplitEpi.cechNerve.sectionEndomorphism.homotopy
    (f := f) (SplitEpi.mk s hs) :
  SimplicialObject.Homotopy
    (SplitEpi.cechNerve.sectionEndomorphism.map (SplitEpi.mk s hs))
    (𝟙 (Arrow.mk f).cechNerve))

#check SplitEpi.cechNerve.sectionEndomorphism.homotopic_id (SplitEpi.mk s hs)

/- Lemma 14.26.9 (2): the Čech nerve is homotopy equivalent to the constant simplicial object on
the target of the split epimorphism. -/
@[stacks 019P "Lemma 14.26.9 (2)"]
#check (SplitEpi.cechNerve.augmentation.homotopyEquiv (SplitEpi.mk s hs) :
  SimplicialObject.HomotopyEquiv
    (Arrow.mk f).cechNerve ((SimplicialObject.const C).obj X))

#check SplitEpi.cechNerve.augmentation.homotopyEquiv.hom (SplitEpi.mk s hs)
#check SplitEpi.cechNerve.augmentation.homotopyEquiv.inv (SplitEpi.mk s hs)

end CategoryTheory
