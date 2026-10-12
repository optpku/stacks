/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

/-!
# Relative pseudo-coherence for scheme modules

This file relates fixed-degree relative pseudo-coherence of a scheme module to the
corresponding property of its degree-zero derived object and records the low-degree criteria.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- Relative `m`-pseudo-coherence of a scheme module through its degree-zero derived object. -/
abbrev IsMPseudoCoherentOver (F : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] (m : ℤ) : Prop :=
  ModuleDerived.IsMPseudoCoherentOver f
    ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F) m

/-- The module predicate is the relative fixed-degree predicate of the degree-zero derived
realization. -/
theorem isMPseudoCoherentOver_iff_single (F : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] (m : ℤ) :
    F.IsMPseudoCoherentOver f m ↔
      ModuleDerived.IsMPseudoCoherentOver f
        ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F) m := sorry

/-- Relative pseudo-coherence of a scheme module through its degree-zero derived object. -/
abbrev IsPseudoCoherentOver (F : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] : Prop :=
  ModuleDerived.IsPseudoCoherentOver f
    ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F)

/-- The module predicate is relative pseudo-coherence of its degree-zero derived
realization. -/
theorem isPseudoCoherentOver_iff_single (F : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    F.IsPseudoCoherentOver f ↔
      ModuleDerived.IsPseudoCoherentOver f
        ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F) := sorry

/-- Relative pseudo-coherence of a scheme module is equivalent to relative
`m`-pseudo-coherence in every degree. -/
theorem isPseudoCoherentOver_iff_forall_m (F : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    F.IsPseudoCoherentOver f ↔ ∀ m : ℤ, F.IsMPseudoCoherentOver f m := sorry

/-- Every scheme module is relatively `m`-pseudo-coherent for a positive bound `m` over a
locally finite type morphism. -/
theorem isMPseudoCoherentOver_of_pos (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (m : ℤ) (hm : 0 < m) : F.IsMPseudoCoherentOver f m := sorry

/-- Relative `0`-pseudo-coherence of a scheme module is equivalent to finite type. -/
theorem isMPseudoCoherentOver_zero_iff (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) : F.IsMPseudoCoherentOver f 0 ↔ F.IsFiniteType := sorry

/-- Relative `(-1)`-pseudo-coherence of a scheme module is equivalent to quasi-coherence
together with relative finite presentation. -/
theorem isMPseudoCoherentOver_minusOne_iff (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) :
    F.IsMPseudoCoherentOver f (-1) ↔ F.IsQuasicoherent ∧ F.IsFinitePresentationOver f := sorry

end AlgebraicGeometry.Scheme.Modules
