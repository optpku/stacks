module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.Functoriality
public import stacks_project.Chap62.Lemma_62_8_2_Effective
public import stacks_project.Chap62.Lemma_62_8_2_Operations

/-!
# Functoriality of effective relative cycles

Restriction, base change, flat pullback, and proper pushforward preserve
effectiveness of relative `r`-cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-Lemma 62.8.2-/
@[stacks 0H5S] #check
  (AlgebraicGeometry.RelativeCycle.isEffective_restrict :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}
      [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
        {α : f.FiberCycleFamily r},
        AlgebraicGeometry.RelativeCycle.IsRelative α →
        AlgebraicGeometry.RelativeCycle.IsEffective α →
        ∀ (U : X.Opens) (V : S.Opens) (φ : U.toScheme ⟶ V.toScheme),
          ∀ (hφ : φ ≫ V.ι = U.ι ≫ f),
          @AlgebraicGeometry.RelativeCycle.IsEffective _ _ φ
            (AlgebraicGeometry.RelativeCycle.locallyOfFiniteType_restriction f U V φ hφ) _
            (AlgebraicGeometry.RelativeCycle.restrict U V φ hφ α))

#check AlgebraicGeometry.RelativeCycle.isEffective_baseChange
#check AlgebraicGeometry.RelativeCycle.isEffective_flatPullback
#check AlgebraicGeometry.RelativeCycle.isEffective_pushforward
