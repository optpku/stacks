/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HyperplaneSection
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison

/-!
# Twisted hyperplane-section sequences

This file specializes the canonical hyperplane-section sequence to every integral twist of a
module on projective space.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {n : ℕ}
variable (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)

/-- Twisting first by `d` and then by `-1` is canonically isomorphic to twisting by
`d - 1`. -/
noncomputable def hyperplaneSectionTwistSourceIso
    (ℱ : P.scheme.Modules) (d : ℤ) :
    P.twist (P.twist ℱ d) (-1) ≅ P.twist ℱ (d - 1) :=
  (α_ ℱ
      (@Scheme.Modules.tensorPowerInt P.scheme P.tautologicalSheaf
        P.tautologicalSheaf_isInvertible d)
      (@Scheme.Modules.tensorPowerInt P.scheme P.tautologicalSheaf
        P.tautologicalSheaf_isInvertible (-1))) ≪≫
    (Iso.refl ℱ ⊗ᵢ
      @RingedSpace.InvertiblePower.addIso P.scheme.toRingedSpace P.tautologicalSheaf
        (Scheme.Modules.Invertible.ringedSpaceIsInvertible
          P.tautologicalSheaf_isInvertible) d (-1))

/-- The pushforward of the restriction of the `d`th twist to the zero scheme of a
tautological section. -/
noncomputable abbrev hyperplaneSectionTwistedRestrictionPushforward
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ) :
    P.scheme.Modules :=
  (Scheme.Modules.pushforward (P.tautologicalZeroSchemeι s)).obj
    ((Scheme.Modules.pullback (P.tautologicalZeroSchemeι s)).obj (P.twist ℱ d))

/-- The restriction of the `d`th twist to the zero scheme of a tautological section. -/
noncomputable abbrev hyperplaneSectionTwistedHyperplaneModule
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ) :
    (P.tautologicalZeroScheme s).Modules :=
  (Scheme.Modules.pullback (P.tautologicalZeroSchemeι s)).obj (P.twist ℱ d)

/-- The section-induced morphism from the `(d - 1)`st twist to the `d`th twist. -/
noncomputable def hyperplaneSectionTwistedLeftMap
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ) :
    P.twist ℱ (d - 1) ⟶ P.twist ℱ d :=
  (hyperplaneSectionTwistSourceIso P ℱ d).inv ≫
    hyperplaneSectionTwistMap P (P.twist ℱ d) s

/-- The section-induced map followed by restriction to its zero scheme is zero. -/
theorem hyperplaneSectionTwistedLeft_comp_right
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ) :
    hyperplaneSectionTwistedLeftMap P ℱ s d ≫
        hyperplaneSectionRestrictionMap P (P.twist ℱ d) s =
      0 := sorry

/-- The canonical three-term complex formed by two consecutive integral twists and
restriction to a hyperplane section. -/
noncomputable def hyperplaneSectionTwistedShortComplex
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ) :
    ShortComplex P.scheme.Modules :=
  ShortComplex.mk
    (hyperplaneSectionTwistedLeftMap P ℱ s d)
    (hyperplaneSectionRestrictionMap P (P.twist ℱ d) s)
    (hyperplaneSectionTwistedLeft_comp_right P ℱ s d)

/-- If the hyperplane-section sequence of a module is short exact, then its canonical
integral-twist sequence is short exact in every degree. -/
theorem hyperplaneSectionTwistedShortExactFor_of_hyperplaneSectionShortExact
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections)
    (hℱ : hyperplaneSectionShortExactFor P ℱ s) (d : ℤ) :
    (hyperplaneSectionTwistedShortComplex P ℱ s d).ShortExact := sorry

end AlgebraicGeometry
