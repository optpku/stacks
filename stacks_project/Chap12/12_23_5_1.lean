/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives
public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms
public import Mathlib.Algebra.Homology.HomologicalComplex
import StacksCheckRecall

@[expose] public section
open CategoryTheory CategoryTheory.Limits

universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
variable (p : ℤ)

namespace StacksEquation012G

/-- Intrinsic cycles lie below the displayed intersection whenever that intersection exists. -/
theorem kernel_le_intersection (Z : Subobject (K.X PUnit.unit).obj)
    (hZ : IsGLB (Set.range fun r : ℕ ↦
      FilteredObject.Hom.cycleRepresentative (K.d PUnit.unit PUnit.unit) r p) Z) :
    FilteredObject.Hom.kernelRepresentative (K.d PUnit.unit PUnit.unit) p ≤ Z := by
  apply hZ.2
  rintro _ ⟨r, rfl⟩
  apply sup_le_sup_right
  apply le_inf inf_le_right
  apply le_trans inf_le_left
  apply Subobject.le_of_factors
  apply pullback_factors
  simpa only [kernelSubobject_arrow_comp] using
    (Subobject.factors_zero : ((K.X PUnit.unit).filtration.stage (p + r)).Factors
      (0 : (kernelSubobject (K.d PUnit.unit PUnit.unit).hom : C) ⟶ (K.X PUnit.unit).obj))

end StacksEquation012G

/- 12.23.5.1: the inequality requires existence of this intersection, not completeness of all
subobject lattices. The page index is nonnegative; p remains an arbitrary integer. -/
@[stacks 012G] #check
  (StacksEquation012G.kernel_le_intersection K p :
    ∀ (Z : Subobject (K.X PUnit.unit).obj),
      IsGLB (Set.range fun r : ℕ ↦
        ((K.X PUnit.unit).filtration.stage p ⊓
          (Subobject.pullback (K.d PUnit.unit PUnit.unit).hom).obj
            ((K.X PUnit.unit).filtration.stage (p + r))) ⊔
              (K.X PUnit.unit).filtration.stage (p + 1)) Z →
      (kernelSubobject (K.d PUnit.unit PUnit.unit).hom ⊓ (K.X PUnit.unit).filtration.stage p) ⊔
        (K.X PUnit.unit).filtration.stage (p + 1) ≤ Z)

variable [CompleteLattice (Subobject (K.X PUnit.unit).obj)]

/- 12.23.5.1: intrinsic cycles, with the filtration-negligible summand, lie in
every finite-page cycle stage of the given filtered differential object. -/
#check
  (FilteredObject.Hom.Representative.Cycle.kernel_le_eventual
      (K.d PUnit.unit PUnit.unit) p :
    (kernelSubobject (K.d PUnit.unit PUnit.unit).hom ⊓ (K.X PUnit.unit).filtration.stage p) ⊔
        (K.X PUnit.unit).filtration.stage (p + 1) ≤
      ⨅ r : ℕ, ((K.X PUnit.unit).filtration.stage p ⊓
        (Subobject.pullback (K.d PUnit.unit PUnit.unit).hom).obj
          ((K.X PUnit.unit).filtration.stage (p + r))) ⊔
            (K.X PUnit.unit).filtration.stage (p + 1))
