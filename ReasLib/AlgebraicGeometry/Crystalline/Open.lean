/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime]

/-- The prime remains locally nilpotent on every open subscheme of the source
of a prime-local crystalline base. -/
theorem Base.open_prime_nilpotent (B : Base.{u} p) (U : Opens B.source) :
    ∀ V : U.toScheme.affineOpens, IsNilpotent (p : Γ(U.toScheme, V)) := sorry

/-- Restriction of a prime-local crystalline base to an open subscheme of its source
retains the divided-power base and restricts the map to its closed fibre. -/
def Base.restrictOpen (B : Base.{u} p) (U : Opens B.source) : Base.{u} p where
  scheme := B.scheme
  ideal := B.ideal
  quasiCoherent := B.quasiCoherent
  dividedPowers := B.dividedPowers
  compatible := B.compatible
  toSpec := B.toSpec
  source := U.toScheme
  sourceToClosed := U.ι ≫ B.sourceToClosed
  prime_nilpotent := B.open_prime_nilpotent U

/-- Open restriction retains the ambient scheme and has the open source with its
restricted closed-fibre map. -/
theorem Base.restrictOpen_spec (B : Base.{u} p) (U : Opens B.source) :
    (B.restrictOpen U).scheme = B.scheme ∧
    (B.restrictOpen U).source = U.toScheme ∧
    (B.restrictOpen U).sourceToClosed = U.ι ≫ B.sourceToClosed :=
  ⟨rfl, rfl, rfl⟩

/-- The inclusion of an open source is compatible with the closed-fibre map of
the identity divided-power base morphism. -/
theorem Ringed.openInclusion_square (B : Base.{u} p) (U : Opens B.source) :
    U.ι ≫ B.sourceToClosed =
      (B.restrictOpen U).sourceToClosed ≫
        (DividedPowerScheme.Hom.id B.dividedPowerScheme).zeroFiberMap := sorry

/-- The inclusion of an open source induces a morphism of crystalline ringed topoi
over the unchanged divided-power base. -/
def Ringed.openInclusion (B : Base.{u} p) (U : Opens B.source) :
    RingedSite.ToposHom (B.restrictOpen U).ringedSite B.ringedSite :=
  Ringed.morphism (B.restrictOpen U) B (DividedPowerScheme.Hom.id B.dividedPowerScheme)
    (by exact Category.id_comp B.toSpec) U.ι (Ringed.openInclusion_square B U)

end AlgebraicGeometry.Scheme.Crystalline
