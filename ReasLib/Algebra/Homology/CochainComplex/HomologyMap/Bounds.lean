module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded ranges for maps on cohomology

This leaf names the two independent range conditions that commonly occur in truncation and
lifting arguments.  They are properties of a cochain map, rather than of a particular derived
or mapping-cone construction.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

noncomputable section

universe v u

namespace CochainComplex.HomologyMap

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex A ℤ}

/-- The map on cohomology induced by `f` is an isomorphism in every degree strictly above `n`. -/
@[stacks 064E "cohomology isomorphisms above a bound"]
def IsIsoAbove (f : K ⟶ L) (n : ℤ) : Prop :=
  ∀ i : ℤ, n < i → IsIso (homologyMap f i)

/-- The map on cohomology induced by `f` is an epimorphism in degree `n`. -/
@[stacks 064E "cohomology epimorphism at a bound"]
def IsEpiAt (f : K ⟶ L) (n : ℤ) : Prop :=
  Epi (homologyMap f n)

namespace IsIsoAbove

/-- Extract the isomorphism condition at a degree above the bound. -/
theorem of_lt {f : K ⟶ L} {n i : ℤ} (h : IsIsoAbove f n) (hi : n < i) :
    IsIso (homologyMap f i) := sorry

end IsIsoAbove

namespace IsEpiAt

/-- Extract the epimorphism condition at the distinguished degree. -/
theorem epi {f : K ⟶ L} {n : ℤ} (h : IsEpiAt f n) :
    Epi (homologyMap f n) := sorry

end IsEpiAt

end CochainComplex.HomologyMap
