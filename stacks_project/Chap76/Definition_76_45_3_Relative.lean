/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_45_2_Characterization

/-!
# Relative pseudo-coherence on algebraic spaces

An object of `D(𝒪_X)` is `m`-pseudo-coherent relative to `Y` when the
equivalent conditions of Lemma 76.45.2 hold, beginning with the test on every
étale scheme square over a locally finite type morphism `f : X ⟶ Y`.
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
    (f : X ⟶ Y) [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  IsMPseudoCoherentOver.everyEtaleSquare f E m

/-- Relative `m`-pseudo-coherence is the étale-square test of Lemma 76.45.2. -/
theorem isMPseudoCoherentOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    IsMPseudoCoherentOver f E m ↔ IsMPseudoCoherentOver.everyEtaleSquare f E m :=
  sorry

/-- On any étale scheme square over `f`, relative `m`-pseudo-coherence of `E`
yields the affine-open `RΓ` test of `E|_U` against `V`. -/
theorem isMPseudoCoherentOver_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {E : ModuleDerived X} {m : ℤ}
    (h : IsMPseudoCoherentOver f E m) (sq : EtaleSquare f)
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] :
    IsMPseudoCoherentOver.onEtaleSquare sq E m :=
  sorry

/-- For `E` in `D_QCoh(𝒪_X)`, relative `m`-pseudo-coherence is equivalent to the
existence of a surjective étale scheme square on which the `RΓ` test holds. -/
theorem isMPseudoCoherentOver_iff_existsSurjectiveEtaleSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E)
    (m : ℤ) :
    IsMPseudoCoherentOver f E m ↔
      IsMPseudoCoherentOver.existsSurjectiveEtaleSquare f E m :=
  sorry

/-- For `E` in `D_QCoh(𝒪_X)`, relative `m`-pseudo-coherence is equivalent to the
affine `RΓ` test on every affine étale scheme square. -/
theorem isMPseudoCoherentOver_iff_everyAffineSections {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E)
    (m : ℤ) :
    IsMPseudoCoherentOver f E m ↔
      IsMPseudoCoherentOver.everyAffineSections f E m :=
  sorry

/-- An object `E` of `D(𝒪_X)` is pseudo-coherent relative to `Y` if it is
`m`-pseudo-coherent relative to `Y` for every integer `m`. -/
abbrev IsPseudoCoherentOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (E : ModuleDerived X) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherentOver f E m

/-- Relative pseudo-coherence is equivalent to relative `m`-pseudo-coherence in
every degree. -/
theorem isPseudoCoherentOver_iff_forall_mPseudoCoherentOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (E : ModuleDerived X) :
    IsPseudoCoherentOver f E ↔ ∀ m : ℤ, IsMPseudoCoherentOver f E m :=
  sorry

/-- Relative pseudo-coherence of `E` over `Y` yields relative `m`-pseudo-coherence
in every degree. -/
theorem isPseudoCoherentOver_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {E : ModuleDerived X}
    (h : IsPseudoCoherentOver f E) (m : ℤ) : IsMPseudoCoherentOver f E m :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
