/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- 29.52.2.1: if `f : X ⟶ S` is locally of finite type, `S` is locally Noetherian, `x : X` has
image `s = f x`, and `E` is the maximum of the transcendence degrees
`trdeg_{κ(f ξ)} κ(ξ)` over the generic points `ξ` of the irreducible components of `X`
containing `x`, then
`dim (𝒪_{X, x}) + trdeg_{κ(s)} κ(x) ≤ dim (𝒪_{S, s}) + E`, equivalently
`dim (𝒪_{X, x}) ≤ dim (𝒪_{S, s}) + E - trdeg_{κ(s)} κ(x)`. -/
@[stacks 0BAF] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.stalk_add_trdeg_le_genericMax :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
      (x : X) (E : ℕ),
      IsGreatest
          {n : ℕ |
            ∃ Z : irreducibleComponents X,
              x ∈ (Z : Set X) ∧
                n = f.residueFieldTrdegAt (genericPoints.ofComponent Z)} E →
        ringKrullDim (X.presheaf.stalk x) + f.residueFieldTrdegAt x ≤
          ringKrullDim (S.presheaf.stalk (f x)) + E)
