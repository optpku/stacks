module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Convergence
public import ReasLib.Order.Filtration

/-!
# Representative Criteria for Filtered Differential Objects

This leaf relates the intrinsic convergence predicates for a filtered differential object to
the cycle and boundary representatives inside its underlying object.  It is the one-object
analogue of `Filtration/Complex/ConvergenceRepresentatives`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

namespace Homology.Filtration

/-- The representative in the underlying object of the `p`-th stage of the filtration induced
on homology. -/
@[stacks 012J "representatives of the induced homology filtration"]
def representative (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  Order.Filtration.Subquotient.representative (K.X PUnit.unit).filtration
    (imageSubobject (differential K).hom) (kernelSubobject (differential K).hom) p

end Homology.Filtration

section CompleteSubobjects

variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

namespace Homology.Filtration

/-- The representative criterion for separatedness and exhaustiveness of the filtration induced
on the homology of a filtered differential object. -/
@[stacks 012J "representative criterion for the induced homology filtration"]
def criterion : Prop :=
  Order.Filtration.Subquotient.IsSeparatedExhaustive (K.X PUnit.unit).filtration
    (imageSubobject (differential K).hom) (kernelSubobject (differential K).hom)

/-- The representative criterion is equivalent to separatedness and exhaustiveness of the
induced homology filtration. -/
@[stacks 012J]
theorem criterion_iff :
    criterion K ↔ IsSeparatedExhaustive K := sorry

end Homology.Filtration

namespace Homology.Representative

/-- The canonical representative criterion for weak convergence of a filtered differential
object.  This is the complete-lattice specialization of the explicit-representative core. -/
@[stacks 012J "canonical representative criterion for weak convergence"]
def IsWeak : Prop :=
  Homology.Convergence.IsWeakAlong K
    (FilteredObject.Hom.LimitRepresentatives.canonical (differential K))

namespace IsWeak

/-- Extract the canonical eventual-boundary equality from the representative criterion. -/
@[stacks 012J "canonical weak convergence boundary equality"]
theorem boundary_eq (hK : Homology.Representative.IsWeak K) (p : ℤ) :
    LimitPage.Representative.boundary K p = Homology.Representative.boundary K p := sorry

/-- Extract the canonical eventual-cycle equality from the representative criterion. -/
@[stacks 012J "canonical weak convergence cycle equality"]
theorem cycle_eq (hK : Homology.Representative.IsWeak K) (p : ℤ) :
    Homology.Representative.cycle K p = LimitPage.Representative.cycle K p := sorry

/-- Build the canonical representative criterion from its boundary and cycle equalities. -/
@[stacks 012J "canonical weak convergence from representative equalities"]
theorem of_equalities
    (hB : ∀ p : ℤ,
      LimitPage.Representative.boundary K p = Homology.Representative.boundary K p)
    (hZ : ∀ p : ℤ,
      Homology.Representative.cycle K p = LimitPage.Representative.cycle K p) :
    Homology.Representative.IsWeak K := sorry

/-- Under complete subobject lattices, weak convergence is equivalent to its canonical
representative criterion. -/
@[stacks 012J "weak convergence iff the canonical representative criterion"]
theorem iff_convergence :
    Homology.Representative.IsWeak K ↔ Homology.Convergence.IsWeak K := sorry

end IsWeak

end Homology.Representative

namespace Homology.Convergence

/-- A filtered differential object abuts to homology exactly when the eventual representatives
give weak convergence and the induced homology filtration satisfies its representative
criterion. -/
@[stacks 012J "abutment iff the representative criteria hold"]
theorem abuts_iff :
    Abuts K ↔ IsWeak K ∧ Homology.Filtration.criterion K := sorry

end Homology.Convergence

namespace Homology.Representative.IsWeak

/-- In the complete-lattice specialization, abutment is exactly the canonical representative
criterion together with the representative criterion for the induced homology filtration. -/
@[stacks 012J "abutment iff canonical representative criteria hold"]
theorem abuts_iff :
    Homology.Convergence.Abuts K ↔ Homology.Representative.IsWeak K ∧
      Homology.Filtration.criterion K := sorry

end Homology.Representative.IsWeak

end CompleteSubobjects

end HomologicalComplex.Filtered
end CategoryTheory
