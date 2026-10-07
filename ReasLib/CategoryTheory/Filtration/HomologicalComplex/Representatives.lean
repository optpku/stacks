module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Homology
public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives

/-!
# Representatives of a Filtered Differential Object

This leaf owns the morphism-level representatives attached to a filtered differential object.
They are independent of a choice or construction of an associated spectral sequence, so both
finite-page and convergence APIs import this module directly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/-- The distinguished filtered endomorphism of a filtered differential object. -/
@[stacks 012C "filtered differential"]
abbrev differential : K.X PUnit.unit ⟶ K.X PUnit.unit :=
  K.d PUnit.unit PUnit.unit

namespace Homology.Representative

/-- The intrinsic cycle representative `Homology.Representative.cycle K p`. -/
@[stacks 012I "intrinsic homology cycle representative"]
abbrev cycle (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  (differential K).kernelRepresentative p

/-- The intrinsic boundary representative `Homology.Representative.boundary K p`. -/
@[stacks 012I "intrinsic homology boundary representative"]
abbrev boundary (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  (differential K).imageRepresentative p

end Homology.Representative

section CompleteSubobjects

variable [CompleteLattice (Subobject ((K.X PUnit.unit).obj))]

namespace LimitPage.Representative

/-- The eventual cycle representative obtained as the infimum of finite cycle stages. -/
@[stacks 012J "eventual cycle representative"]
noncomputable abbrev cycle (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  (differential K).eventualCycleRepresentative p

/-- The eventual boundary representative obtained as the supremum of finite boundary stages. -/
@[stacks 012J "eventual boundary representative"]
noncomputable abbrev boundary (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  (differential K).eventualBoundaryRepresentative p

end LimitPage.Representative

end CompleteSubobjects

end HomologicalComplex.Filtered
end CategoryTheory
