/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Japanese and Nagata schemes

This file owns the basic scheme-level Japanese, universally Japanese, and
Nagata predicates.  They are expressed through the neutral
`Scheme.HasRingPropertyLocally` owner whenever the ring condition is genuinely
affine local.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- On an integral scheme, a nonempty affine open has Japanese section ring
when its section ring is `N-2` with the domain structure induced by
integrality. -/
abbrev affineOpenSectionsIsN2Ring (X : Scheme.{u}) [IsIntegral X] (U : X.affineOpens)
    (hU : Nonempty U) : Prop :=
  @IsN2Ring (Γ(X, U)) inferInstance
    (@AlgebraicGeometry.IsIntegral.component_integral X inferInstance (U : X.Opens) hU)

/-- An integral scheme is Japanese when every point admits an affine open
neighbourhood whose section ring is `N-2`. -/
@[stacks 033S]
abbrev IsJapanese (X : Scheme.{u}) [IsIntegral X] : Prop :=
  ∀ x : X,
    ∃ U : X.affineOpens,
      ∃ hx : x ∈ (U : X.Opens),
        affineOpenSectionsIsN2Ring X U ⟨⟨x, hx⟩⟩

/-- An integral Japanese scheme has an affine `N-2` neighbourhood at every
point. -/
theorem exists_affineOpen_isN2Ring (X : Scheme.{u}) [IsIntegral X] (h : IsJapanese X) (x : X) :
    ∃ U : X.affineOpens,
      ∃ hx : x ∈ (U : X.Opens),
        affineOpenSectionsIsN2Ring X U ⟨⟨x, hx⟩⟩ := sorry

/-- Unfold `IsJapanese` into its affine-open neighbourhood condition. -/
theorem isJapanese_iff (X : Scheme.{u}) [IsIntegral X] :
    IsJapanese X ↔
      ∀ x : X,
        ∃ U : X.affineOpens,
          ∃ hx : x ∈ (U : X.Opens),
            affineOpenSectionsIsN2Ring X U ⟨⟨x, hx⟩⟩ := sorry

/-- A scheme is universally Japanese when the universally Japanese ring
property holds affine locally. -/
@[stacks 033S]
abbrev UniversallyJapanese (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ UniversallyJapaneseRing.{u, u} A)

/-- A universally Japanese scheme has an affine universally Japanese
neighbourhood at every point. -/
theorem exists_affineOpen_universallyJapaneseRing (X : Scheme.{u}) [UniversallyJapanese X]
    (x : X) :
    ∃ U : X.affineOpens,
      x ∈ (U : X.Opens) ∧ UniversallyJapaneseRing.{u, u} (Γ(X, (U : X.Opens))) := sorry

/-- Unfold `UniversallyJapanese` into its affine-open neighbourhood condition. -/
theorem universallyJapanese_iff (X : Scheme.{u}) :
    UniversallyJapanese X ↔
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ (U : X.Opens) ∧ UniversallyJapaneseRing.{u, u} (Γ(X, (U : X.Opens))) := sorry

/-- A scheme is Nagata when the Nagata ring property holds affine locally. -/
@[stacks 033S]
abbrev Nagata (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ NagataRing A)

/-- A Nagata scheme has an affine Nagata neighbourhood at every point. -/
theorem exists_affineOpen_nagataRing (X : Scheme.{u}) [Nagata X] (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ NagataRing (Γ(X, (U : X.Opens))) := sorry

/-- Unfold `Nagata` into its affine-open neighbourhood condition. -/
theorem nagata_iff (X : Scheme.{u}) :
    Nagata X ↔
      ∀ x : X,
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ NagataRing (Γ(X, (U : X.Opens))) := sorry

end AlgebraicGeometry.Scheme
