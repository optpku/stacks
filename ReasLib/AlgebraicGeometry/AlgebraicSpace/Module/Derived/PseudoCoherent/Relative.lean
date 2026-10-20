module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative.Etale

/-!
# Relative pseudo-coherence on algebraic spaces

Relative `m`-pseudo-coherence is the test on every étale scheme square over a
locally finite type morphism `f : X ⟶ Y`. The predicate is defined for arbitrary
derived modules; on objects with quasi-coherent cohomology it agrees with the
equivalent surjective-square and affine derived-sections criteria.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- An object `E` of `D(𝒪_X)` is `m`-pseudo-coherent relative to `Y` if
`E|_U` is `m`-pseudo-coherent relative to `V` on every étale scheme square
over `f`. -/
abbrev IsMPseudoCoherentOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  IsMPseudoCoherentOver.everyEtaleSquare f E m

/-- Relative `m`-pseudo-coherence is equivalent to the test on every étale scheme square. -/
theorem isMPseudoCoherentOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    IsMPseudoCoherentOver f E m ↔ IsMPseudoCoherentOver.everyEtaleSquare f E m :=
  sorry

/-- An object `E` of `D(𝒪_X)` is pseudo-coherent relative to `Y` if it is
`m`-pseudo-coherent relative to `Y` for every integer `m`. -/
abbrev IsPseudoCoherentOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherentOver f E m

/-- Relative pseudo-coherence is equivalent to relative `m`-pseudo-coherence in
every degree. -/
theorem isPseudoCoherentOver_iff_forall_mPseudoCoherentOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (E : ModuleDerived X) :
    IsPseudoCoherentOver f E ↔ ∀ m : ℤ, IsMPseudoCoherentOver f E m :=
  sorry

/-- Relative pseudo-coherence of `E` over `Y` yields relative `m`-pseudo-coherence
in every degree. -/
theorem isPseudoCoherentOver_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] {E : ModuleDerived X}
    (h : IsPseudoCoherentOver f E) (m : ℤ) : IsMPseudoCoherentOver f E m :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
