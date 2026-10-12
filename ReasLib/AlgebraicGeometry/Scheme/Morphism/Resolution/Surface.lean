/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.RingTheory.Normal.Local

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y]
variable (h_dimension : topologicalKrullDim Y = 2)

include h_dimension

/-- For a two-dimensional integral Noetherian scheme, a regular alteration exists exactly when a
resolution of singularities exists. -/
theorem regularAlteration_iff_resolution :
    (∃ (X : Scheme.{u}) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ Regular X) ↔
    ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsResolution f := sorry

/-- For a two-dimensional integral Noetherian scheme, a regular alteration exists exactly when a
resolution by normalized blowups exists. -/
theorem regularAlteration_iff_normalizedBlowups :
    (∃ (X : Scheme.{u}) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ Regular X) ↔
    HasResolutionByNormalizedBlowups Y h_dimension := sorry

/-- For a two-dimensional integral Noetherian scheme, a regular alteration exists exactly when its
normalization is finite, has finitely many singular points, and has normal completed local rings
at those points. -/
theorem regularAlteration_iff_finiteNormalization_normalCompletions :
    (∃ (X : Scheme.{u}) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ Regular X) ↔
    IsFinite (normalizationToOfIsNoetherian Y) ∧
      (Sing(normalizationOfIsNoetherian Y)).Finite ∧
      ∀ y : normalizationOfIsNoetherian Y,
        y ∈ Sing(normalizationOfIsNoetherian Y) →
          IsNormalRing (AdicCompletion
            (IsLocalRing.maximalIdeal
              ((normalizationOfIsNoetherian Y).presheaf.stalk y))
            ((normalizationOfIsNoetherian Y).presheaf.stalk y)) := sorry

end AlgebraicGeometry.Scheme
