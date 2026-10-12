/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.OpenExtension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.42.5: an `S`-morphism from an open subscheme `U` of `X` to a proper
`S`-scheme extends to an open neighbourhood of a closure point `x` when the stalk at `x` is a
valuation ring and `X` is reduced with finitely many irreducible components or Noetherian. -/
@[stacks 0BX7] #check
  (AlgebraicGeometry.exists_openExtensionAtPoint_of_isProper_of_stalk_valuationRing :
    ∀ {S X Y : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S} {x : X} {U : X.Opens}
      (f : U.toScheme ⟶ Y) (hf_over : f ≫ fY = U.ι ≫ fX)
      (hx_closure : x ∈ closure (U : Set X))
      [IsProper fY]
      [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)]
      (hX : (IsReduced X ∧ Finite (irreducibleComponents X)) ∨ IsNoetherian X),
      ∃ (U' : X.Opens) (hUU' : U ≤ U') (_ : x ∈ U') (f' : U'.toScheme ⟶ Y),
        f' ≫ fY = U'.ι ≫ fX ∧ X.homOfLE hUU' ≫ f' = f)
