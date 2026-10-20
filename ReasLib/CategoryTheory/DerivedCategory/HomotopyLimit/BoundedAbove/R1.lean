module

public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.BoundedAbove
public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sharp Upper Bounds from Vanishing of `R¹lim`

The only possible extra top cohomology of a uniformly bounded sequential homotopy limit is the
first derived inverse limit of the top cohomology tower.  Vanishing of that object recovers the
original upper bound.
@stack 09AU
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe w v u

namespace CategoryTheory.HomotopyLimit.IsOf

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C]
variable [HasLimitsOfShape ℕᵒᵖ C]
variable {Ksys : SequentialInverseSystem (DerivedCategory C)}
variable {K : DerivedCategory C}

/-- Uniform stagewise membership in `D^{≤ b}` and vanishing of the top `R¹lim` imply that the
homotopy limit itself belongs to `D^{≤ b}`. -/
@[stacks 09AU "sharp upper bound from vanishing of the first derived limit"]
theorem isLE_of_r1_zero (hK : HomotopyLimit.IsOf Ksys K) {b : ℤ}
    (h_bound : ∀ n : ℕ, (Ksys.obj (Opposite.op n)).IsLE b)
    (h_r1 : IsZero
      (SequentialInverseSystem.Milnor.ProductCone.canonicalR1
        (Ksys ⋙ DerivedCategory.homologyFunctor C b))) :
    K.IsLE b := sorry

/-- If the transition maps on top cohomology are epimorphisms, a uniform upper bound is
preserved by the homotopy limit. -/
@[stacks 09AU "sharp upper bound from epimorphic top cohomology transitions"]
theorem isLE_of_epi_homology (hK : HomotopyLimit.IsOf Ksys K) {b : ℤ}
    (h_bound : ∀ n : ℕ, (Ksys.obj (Opposite.op n)).IsLE b)
    (h_epi : ∀ n : ℕ,
      Epi ((DerivedCategory.homologyFunctor C b).map (Ksys.stepMap n))) :
    K.IsLE b := sorry

end CategoryTheory.HomotopyLimit.IsOf
