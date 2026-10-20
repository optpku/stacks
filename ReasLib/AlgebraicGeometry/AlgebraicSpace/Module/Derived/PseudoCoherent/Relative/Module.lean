module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative

/-!
# Relative pseudo-coherence of modules on algebraic spaces

An `𝒪_X`-module is `m`-pseudo-coherent relative to `Y` when its degree-zero
derived realization is `m`-pseudo-coherent relative to `Y`. These predicates
are defined for arbitrary modules and in particular apply to quasi-coherent
modules through their degree-zero objects with quasi-coherent cohomology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Relative `m`-pseudo-coherence of an `𝒪_X`-module through its degree-zero
derived object. -/
abbrev IsMPseudoCoherentOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f] (m : ℤ) : Prop :=
  ModuleDerived.IsMPseudoCoherentOver f
    ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F) m

/-- The module predicate is relative `m`-pseudo-coherence of the degree-zero
derived realization. -/
theorem isMPseudoCoherentOver_iff_single {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f] (m : ℤ) :
    IsMPseudoCoherentOver F f m ↔
      ModuleDerived.IsMPseudoCoherentOver f
        ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F) m :=
  sorry

/-- Relative pseudo-coherence of an `𝒪_X`-module through its degree-zero derived
object. -/
abbrev IsPseudoCoherentOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f] : Prop :=
  ModuleDerived.IsPseudoCoherentOver f
    ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F)

/-- The module predicate is relative pseudo-coherence of the degree-zero derived
realization. -/
theorem isPseudoCoherentOver_iff_single {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    IsPseudoCoherentOver F f ↔
      ModuleDerived.IsPseudoCoherentOver f
        ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F) :=
  sorry

/-- Relative pseudo-coherence of an `𝒪_X`-module is equivalent to relative
`m`-pseudo-coherence in every degree. -/
theorem isPseudoCoherentOver_iff_forall_m {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    IsPseudoCoherentOver F f ↔ ∀ m : ℤ, IsMPseudoCoherentOver F f m :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
