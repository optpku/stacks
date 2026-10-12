/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Dimension

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Lemma 42.16.1 (1): for an integral closed subscheme of an integral scheme locally of finite
type over `(S, δ)`, codimension one is equivalent to a one-step drop in `δ`-dimension. -/
@[stacks 02RK] #check
  (AlgebraicGeometry.Scheme.Hom.coheight_eq_one_iff_deltaDimension_eq_sub_one :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X]
      (Z : X.IdealSheafData) [IsIntegral Z.subscheme],
      Order.coheight
          (toIrreducibleCloseds (Z.subschemeι (genericPoint Z.subscheme))) = 1 ↔
        p.deltaDimension δ
            (toIrreducibleCloseds (Z.subschemeι (genericPoint Z.subscheme))) =
          p.deltaDimension δ (toIrreducibleCloseds (genericPoint X)) - 1)

/- The bundled prime-divisor form of the codimension-one dimension formula. -/
#check
  (AlgebraicGeometry.PrimeDivisor.deltaDimension_eq_sub_one :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X]
      (Z : AlgebraicGeometry.PrimeDivisor X),
      p.deltaDimension δ Z.support =
        p.deltaDimension δ (toIrreducibleCloseds (genericPoint X)) - 1)

/- Lemma 42.16.1 (2): every irreducible component of an effective Cartier divisor on an
integral scheme has `δ`-dimension one less than the ambient scheme. -/
@[stacks 02RK] #check
  (AlgebraicGeometry.Scheme.Hom.effectiveCartierComponent_deltaDimension_eq_sub_one :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X]
      (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
      (C : irreducibleComponents D.subscheme),
      p.deltaDimension δ
          (toIrreducibleCloseds (D.subschemeι (genericPoints.ofComponent C).1)) =
        p.deltaDimension δ (toIrreducibleCloseds (genericPoint X)) - 1)
