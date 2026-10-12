/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Representatives
public import ReasLib.CategoryTheory.Filtration.Lattice
public import ReasLib.CategoryTheory.Filtration.Morphism.LimitRepresentatives

/-!
# Convergence for Filtered Differential Objects

This file owns weak convergence and abutment for a filtered differential object.  These
properties depend only on the filtered differential object and its eventual representative
subobjects, not on a chosen presentation of an associated spectral sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

section CompleteSubobjects

variable [CompleteLattice (Subobject ((underlying K).homology PUnit.unit))]

namespace Homology.Filtration

/-- Separatedness and exhaustiveness of the induced homology filtration are respectively the
vanishing of its intersection and the exhaustion of its ambient homology object. -/
theorem isSeparatedExhaustive_iff :
    IsSeparatedExhaustive K ↔
      (⨅ p : ℤ, (induced K PUnit.unit).stage p) = ⊥ ∧
        (⨆ p : ℤ, (induced K PUnit.unit).stage p) = ⊤ := sorry

end Homology.Filtration

end CompleteSubobjects

section LimitRepresentatives

namespace Homology.Convergence

/-- Relative to explicit limit representatives, a filtered differential object weakly converges
to homology when the eventual boundary and cycle representatives agree with the intrinsic
homology representatives in every filtration degree. -/
@[stacks 012I "weak convergence along explicit limit representatives"]
def IsWeakAlong
    (L : FilteredObject.Hom.LimitRepresentatives (differential K)) : Prop :=
  ∀ p : ℤ,
    L.boundary p = Homology.Representative.boundary K p ∧
      Homology.Representative.cycle K p = L.cycle p

namespace IsWeakAlong

/-- Extract the eventual-boundary equality at one filtration degree from weak convergence along
the selected representatives. -/
@[stacks 012I "weak convergence boundary equality along explicit representatives"]
theorem boundary_eq
    {L : FilteredObject.Hom.LimitRepresentatives (differential K)}
    (hK : IsWeakAlong K L) (p : ℤ) :
    L.boundary p = Homology.Representative.boundary K p := sorry

/-- Extract the eventual-cycle equality at one filtration degree from weak convergence along the
selected representatives. -/
@[stacks 012I "weak convergence cycle equality along explicit representatives"]
theorem cycle_eq
    {L : FilteredObject.Hom.LimitRepresentatives (differential K)}
    (hK : IsWeakAlong K L) (p : ℤ) :
    Homology.Representative.cycle K p = L.cycle p := sorry

/-- Build weak convergence along selected representatives from its boundary and cycle
equalities. -/
@[stacks 012I "weak convergence along explicit representatives from equalities"]
theorem of_equalities
    (L : FilteredObject.Hom.LimitRepresentatives (differential K))
    (hB : ∀ p : ℤ,
      L.boundary p = Homology.Representative.boundary K p)
    (hZ : ∀ p : ℤ,
      Homology.Representative.cycle K p = L.cycle p) :
    IsWeakAlong K L := sorry

end IsWeakAlong

/-- A filtered differential object weakly converges to its homology when it admits explicit
eventual representatives satisfying the intrinsic boundary and cycle equalities. -/
@[stacks 012I "weak convergence of a filtered differential object"]
def IsWeak : Prop :=
  ∃ L : FilteredObject.Hom.LimitRepresentatives (differential K), IsWeakAlong K L

namespace IsWeak

/-- Weak convergence along specified representatives supplies unqualified weak convergence. -/
theorem of_along
    {L : FilteredObject.Hom.LimitRepresentatives (differential K)}
    (hL : IsWeakAlong K L) : IsWeak K := sorry

/-- Weak convergence supplies selected representatives along which the intrinsic equalities
hold. -/
@[stacks 012I "explicit limit representatives from weak convergence"]
theorem exists_along (hK : IsWeak K) :
    ∃ L : FilteredObject.Hom.LimitRepresentatives (differential K), IsWeakAlong K L := sorry

end IsWeak

/-- Relative to explicit limit representatives, abutment is weak convergence together with
separatedness and exhaustiveness of the induced homology filtration. -/
@[stacks 012I "abutment along explicit limit representatives"]
def AbutsAlong
    (L : FilteredObject.Hom.LimitRepresentatives (differential K)) : Prop :=
  IsWeakAlong K L ∧ Homology.Filtration.IsSeparatedExhaustive K

namespace AbutsAlong

variable {K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
variable {L : FilteredObject.Hom.LimitRepresentatives (differential K)}

/-- Abutment along selected representatives supplies weak convergence along those same
representatives. -/
theorem isWeak (h : AbutsAlong K L) : IsWeakAlong K L := sorry

/-- Abutment along selected representatives supplies the intrinsic filtration condition. -/
theorem isSeparatedExhaustive (h : AbutsAlong K L) :
    Homology.Filtration.IsSeparatedExhaustive K := sorry

/-- Assemble abutment along selected representatives from weak convergence along those
representatives and the intrinsic filtration condition. -/
theorem of_isWeak
    (hweak : IsWeakAlong K L)
    (hfiltration : Homology.Filtration.IsSeparatedExhaustive K) :
    AbutsAlong K L := sorry

end AbutsAlong

/-- A filtered differential object abuts to its homology when it weakly converges and its induced
homology filtration is separated and exhaustive. -/
@[stacks 012I "abutment of a filtered differential object"]
def Abuts : Prop :=
  IsWeak K ∧ Homology.Filtration.IsSeparatedExhaustive K

namespace Abuts

variable {K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}

/-- An abutment supplies weak convergence. -/
theorem isWeak (h : Abuts K) : IsWeak K := sorry

/-- An abutment supplies separatedness and exhaustiveness of the induced homology filtration. -/
theorem isSeparatedExhaustive (h : Abuts K) :
    Homology.Filtration.IsSeparatedExhaustive K := sorry

/-- Assemble abutment from weak convergence and the intrinsic filtration condition. -/
theorem of_isWeak
    (hweak : IsWeak K)
    (hfiltration : Homology.Filtration.IsSeparatedExhaustive K) :
    Abuts K := sorry

/-- Abutment along specified representatives supplies unqualified abutment. -/
theorem of_along
    {L : FilteredObject.Hom.LimitRepresentatives (differential K)}
    (hL : AbutsAlong K L) : Abuts K := sorry

/-- Abutment supplies selected representatives along which its weak-convergence comparison
holds. -/
@[stacks 012I "explicit limit representatives from abutment"]
theorem exists_along (hK : Abuts K) :
    ∃ L : FilteredObject.Hom.LimitRepresentatives (differential K), AbutsAlong K L := sorry

end Abuts

end Homology.Convergence

end LimitRepresentatives

end HomologicalComplex.Filtered
end CategoryTheory
