module

public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap78.Definition_78_8_1_Action
public import stacks_project.Chap78.Definition_78_9_3_Covering

/-!
# Torsors under group algebraic spaces

This module defines cover-local triviality for a pseudo action of a group
algebraic space and specializes it to the fpqc and five standard algebraic-space
precoverages.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
  (X : Action G)

/-- A pseudo `G`-torsor is trivial on a chosen cover when it has a section over
every member of the cover. A section of `X_{B_i} ⟶ B_i` is the trivial
pseudo `G_{B_i}`-torsor condition of Lemma 78.9.2. -/
def IsTrivialOn {K : Precoverage (AlgebraicSpace S)} (U : B.Cover K) : Prop :=
  ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X)

/-- Triviality on a chosen cover is memberwise existence of sections. -/
theorem isTrivialOn_iff {K : Precoverage (AlgebraicSpace S)} (U : B.Cover K) :
    IsTrivialOn G X U ↔
      ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X) := sorry

/-- A `G`-action is a torsor for `K` when it is a pseudo-torsor and is trivial
on some `K`-cover. -/
structure IsTorsorFor (K : Precoverage (AlgebraicSpace S)) : Prop where
  isPseudoTorsor : Mod.IsPseudoTorsor X
  exists_trivializingCover : ∃ U : B.Cover K, IsTrivialOn G X U

/-- Constructs a torsor for `K` from a pseudo-torsor and a chosen trivializing
cover. -/
def IsTorsorFor.ofTrivializingCover {K : Precoverage (AlgebraicSpace S)}
    (hX : Mod.IsPseudoTorsor X) (U : B.Cover K) (hU : IsTrivialOn G X U) :
    IsTorsorFor G X K where
  isPseudoTorsor := hX
  exists_trivializingCover := ⟨U, hU⟩

/-- The cover-and-sections characterization of a torsor for a precoverage. -/
theorem isTorsorFor_iff (K : Precoverage (AlgebraicSpace S)) :
    IsTorsorFor G X K ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover K,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X) := sorry

/-- A torsor for a precoverage remains a torsor after enlarging the
precoverage. -/
theorem IsTorsorFor.mono {K L : Precoverage (AlgebraicSpace S)} (hKL : K ≤ L)
    (hX : IsTorsorFor G X K) : IsTorsorFor G X L := sorry

/-- A pseudo `G`-torsor that acquires sections on an fpqc covering. -/
abbrev IsTorsor : Prop :=
  IsTorsorFor G X (AlgebraicSpace.fpqcPrecoverage S)

/-- The fpqc cover-and-sections characterization of a principal homogeneous
`G`-space. -/
theorem isTorsor_iff :
    IsTorsor G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover (AlgebraicSpace.fpqcPrecoverage S),
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X) := sorry

/-- A pseudo `G`-torsor that acquires sections in the standard topology `τ`. -/
abbrev IsStandardTorsor (τ : StandardTopology) : Prop :=
  IsTorsorFor G X (AlgebraicSpace.standardPrecoverage S τ)

/-- The cover-and-sections characterization of a torsor for a standard
topology. -/
theorem isStandardTorsor_iff (τ : StandardTopology) :
    IsStandardTorsor G X τ ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S τ),
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X) := sorry

/-- An étale-locally trivial pseudo `G`-torsor. -/
abbrev IsQuasiIsotrivial : Prop :=
  IsStandardTorsor G X .etale

/-- The étale cover-and-sections characterization of quasi-isotriviality. -/
theorem isQuasiIsotrivial_iff :
    IsQuasiIsotrivial G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S .etale),
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X) := sorry

/-- A Zariski-locally trivial pseudo `G`-torsor. -/
abbrev IsLocallyTrivial : Prop :=
  IsStandardTorsor G X .zariski

/-- The Zariski cover-and-sections characterization of local triviality. -/
theorem isLocallyTrivial_iff :
    IsLocallyTrivial G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S .zariski),
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X) := sorry

/-- Every torsor for a standard topology is an fpqc torsor. -/
theorem IsStandardTorsor.isTorsor {τ : StandardTopology}
    (hX : IsStandardTorsor G X τ) : IsTorsor G X := sorry

/-- Every quasi-isotrivial pseudo torsor is an fpqc torsor. -/
theorem IsQuasiIsotrivial.isTorsor
    (hX : IsQuasiIsotrivial G X) : IsTorsor G X := sorry

/-- Every Zariski-locally trivial pseudo torsor is an fpqc torsor. -/
theorem IsLocallyTrivial.isTorsor
    (hX : IsLocallyTrivial G X) : IsTorsor G X := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
