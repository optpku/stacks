/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

/-!
# Definition 28.13.1

The reusable scheme-level Japanese, universally Japanese, and Nagata owners
live in `ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic`.
-/

/- Definition 28.13.1: Japanese, universally Japanese, and Nagata schemes. -/
@[stacks 033S] #check
  (@AlgebraicGeometry.Scheme.IsJapanese :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X], Prop)
#check (AlgebraicGeometry.Scheme.UniversallyJapanese : AlgebraicGeometry.Scheme.{u} → Prop)
#check (AlgebraicGeometry.Scheme.Nagata : AlgebraicGeometry.Scheme.{u} → Prop)

#check (@AlgebraicGeometry.IsIntegral.component_integral :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (h_integral : AlgebraicGeometry.IsIntegral X)
    (U : X.Opens) (hU : Nonempty U), IsDomain Γ(X, U))

#check (@AlgebraicGeometry.Scheme.affineOpenSectionsIsN2Ring :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (h_integral : AlgebraicGeometry.IsIntegral X)
    (U : X.affineOpens) (hU : Nonempty U), Prop)

#check (@AlgebraicGeometry.Scheme.exists_affineOpen_isN2Ring :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (h_integral : AlgebraicGeometry.IsIntegral X)
    (h_japanese : AlgebraicGeometry.Scheme.IsJapanese X) (x : X),
      ∃ U : X.affineOpens,
        ∃ hx : x ∈ (U : X.Opens),
          AlgebraicGeometry.Scheme.affineOpenSectionsIsN2Ring X U ⟨⟨x, hx⟩⟩)

#check (@AlgebraicGeometry.Scheme.isJapanese_iff :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (h_integral : AlgebraicGeometry.IsIntegral X),
    AlgebraicGeometry.Scheme.IsJapanese X ↔
      ∀ x : X,
        ∃ U : X.affineOpens,
          ∃ hx : x ∈ (U : X.Opens),
            AlgebraicGeometry.Scheme.affineOpenSectionsIsN2Ring X U ⟨⟨x, hx⟩⟩)

#check (@AlgebraicGeometry.Scheme.exists_affineOpen_universallyJapaneseRing :
  ∀ (X : AlgebraicGeometry.Scheme.{u})
    (h_universallyJapanese : AlgebraicGeometry.Scheme.UniversallyJapanese X) (x : X),
      ∃ U : X.affineOpens,
        x ∈ (U : X.Opens) ∧ UniversallyJapaneseRing.{u, u} Γ(X, (U : X.Opens)))

#check (@AlgebraicGeometry.Scheme.universallyJapanese_iff :
  ∀ X : AlgebraicGeometry.Scheme.{u},
    AlgebraicGeometry.Scheme.UniversallyJapanese X ↔
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ (U : X.Opens) ∧ UniversallyJapaneseRing.{u, u} Γ(X, (U : X.Opens)))

#check (@AlgebraicGeometry.Scheme.exists_affineOpen_nagataRing :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (h_nagata : AlgebraicGeometry.Scheme.Nagata X) (x : X),
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ NagataRing Γ(X, (U : X.Opens)))

#check (@AlgebraicGeometry.Scheme.nagata_iff :
  ∀ X : AlgebraicGeometry.Scheme.{u},
    AlgebraicGeometry.Scheme.Nagata X ↔
      ∀ x : X,
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ NagataRing Γ(X, (U : X.Opens)))
