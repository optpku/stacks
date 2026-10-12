/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor

/-!
# Torsors under group schemes

This module defines cover-local triviality for a pseudo action of a group scheme and
specializes it to the fpqc and five standard scheme precoverages.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupScheme

variable {S : Scheme.{u}} (G : Grp (Over S)) (X : Mod (Over S) G.X)

/-- A pseudo `G`-torsor is trivial on a chosen cover when it has a section over every
member of the cover. -/
def IsTrivialOn {K : Precoverage Scheme.{u}} (U : S.Cover.{u} K) : Prop :=
  ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X)

/-- Triviality on a chosen cover is memberwise existence of sections. -/
theorem isTrivialOn_iff {K : Precoverage Scheme.{u}} (U : S.Cover.{u} K) :
    IsTrivialOn G X U ↔
      ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) := sorry

/-- A `G`-action is a torsor for `K` when it is a pseudo-torsor and is trivial on
some `K`-cover. -/
structure IsTorsorFor (K : Precoverage Scheme.{u}) : Prop where
  isPseudoTorsor : Mod.IsPseudoTorsor X
  exists_trivializingCover : ∃ U : S.Cover.{u} K, IsTrivialOn G X U

/-- Constructs a torsor for `K` from a pseudo-torsor and a chosen trivializing cover. -/
def IsTorsorFor.ofTrivializingCover {K : Precoverage Scheme.{u}}
    (hX : Mod.IsPseudoTorsor X) (U : S.Cover.{u} K) (hU : IsTrivialOn G X U) :
    IsTorsorFor G X K where
  isPseudoTorsor := hX
  exists_trivializingCover := ⟨U, hU⟩

/-- The cover-and-sections characterization of a torsor for a precoverage. -/
theorem isTorsorFor_iff (K : Precoverage Scheme.{u}) :
    IsTorsorFor G X K ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} K,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) := sorry

/-- A torsor for a precoverage remains a torsor after enlarging the precoverage. -/
theorem IsTorsorFor.mono {K L : Precoverage Scheme.{u}} (hKL : K ≤ L)
    (hX : IsTorsorFor G X K) : IsTorsorFor G X L := sorry

/-- A pseudo `G`-torsor that acquires sections on an fpqc cover. -/
abbrev IsTorsor : Prop :=
  IsTorsorFor G X Scheme.fpqcPrecoverage

/-- The fpqc cover-and-sections characterization of a `G`-torsor. -/
theorem isTorsor_iff :
    IsTorsor G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} Scheme.fpqcPrecoverage,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) := sorry

/-- A pseudo `G`-torsor that acquires sections in the standard topology `τ`. -/
abbrev IsStandardTorsor (τ : StandardTopology) : Prop :=
  IsTorsorFor G X τ.precoverage

/-- The cover-and-sections characterization of a torsor for a standard topology. -/
theorem isStandardTorsor_iff (τ : StandardTopology) :
    IsStandardTorsor G X τ ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} τ.precoverage,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) := sorry

/-- An étale-locally trivial pseudo `G`-torsor. -/
abbrev IsQuasiIsotrivial : Prop :=
  IsStandardTorsor G X .etale

/-- The étale cover-and-sections characterization of quasi-isotriviality. -/
theorem isQuasiIsotrivial_iff :
    IsQuasiIsotrivial G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} StandardTopology.etale.precoverage,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) := sorry

/-- A Zariski-locally trivial pseudo `G`-torsor. -/
abbrev IsLocallyTrivial : Prop :=
  IsStandardTorsor G X .zariski

/-- The Zariski cover-and-sections characterization of local triviality. -/
theorem isLocallyTrivial_iff :
    IsLocallyTrivial G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} StandardTopology.zariski.precoverage,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) := sorry

/-- Every torsor for a standard topology is an fpqc torsor. -/
theorem IsStandardTorsor.isTorsor {τ : StandardTopology}
    (hX : IsStandardTorsor G X τ) : IsTorsor G X := sorry

/-- Every quasi-isotrivial pseudo torsor is an fpqc torsor. -/
theorem IsQuasiIsotrivial.isTorsor
    (hX : IsQuasiIsotrivial G X) : IsTorsor G X := sorry

/-- Every Zariski-locally trivial pseudo torsor is an fpqc torsor. -/
theorem IsLocallyTrivial.isTorsor
    (hX : IsLocallyTrivial G X) : IsTorsor G X := sorry

end AlgebraicGeometry.GroupScheme
