/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen
public import ReasLib.RingTheory.Localization.FractionRing.Jacobson

/-!
# Globally generated invertible modules from affine open complements

This file records the construction of a globally generated invertible module whose section
has a prescribed affine nonvanishing open.
-/

@[expose] public section

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OpenComplement

variable {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]

/-- On an integral separated scheme, a nonempty affine open with finite complement and
one-dimensional Noetherian stalks along the complement is the nonvanishing open of a global
section of a globally generated invertible module. -/
@[stacks 09NB]
theorem exists_globallyGenerated_invertibleModule_sectionNonvanishingOpen
    (U : X.Opens) (hU_affine : IsAffineOpen U) (hU_nonempty : Nonempty U)
    (hFinite : Set.Finite {x : X | x ∉ (U : Set X)})
    (hNoeth : ∀ x : X, x ∉ (U : Set X) → IsNoetherianRing (X.presheaf.stalk x))
    (hDim : ∀ x : X, x ∉ (U : Set X) → ringKrullDim (X.presheaf.stalk x) = 1) :
    ∃ (L : X.Modules) (hL : Modules.Invertible L),
      SheafOfModules.IsGloballyGenerated L ∧
        ∃ s : Γ(L, ⊤), U = hL.sectionNonvanishingOpen s := sorry

end AlgebraicGeometry.Scheme.OpenComplement
