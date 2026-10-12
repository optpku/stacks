/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.OpenComplement
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.38.4: an integral separated scheme with a nonempty affine open whose complement
is finite and has one-dimensional Noetherian stalks admits a globally generated invertible
module with a section whose nonvanishing open is the given affine open. -/
@[stacks 09NB] #check
  (AlgebraicGeometry.Scheme.OpenComplement.exists_globallyGenerated_invertibleModule_sectionNonvanishingOpen :
    ∀ {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
      (U : X.Opens), IsAffineOpen U → Nonempty U →
      Set.Finite {x : X | x ∉ (U : Set X)} →
      (∀ x : X, x ∉ (U : Set X) → IsNoetherianRing (X.presheaf.stalk x)) →
      (∀ x : X, x ∉ (U : Set X) → ringKrullDim (X.presheaf.stalk x) = 1) →
      ∃ (L : X.Modules) (hL : Scheme.Modules.Invertible L),
        SheafOfModules.IsGloballyGenerated L ∧
          ∃ s : Γ(L, ⊤), U = hL.sectionNonvanishingOpen s)
