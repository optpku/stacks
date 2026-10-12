/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity.CohenMacaulay

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open TopCat.Presheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.16.5: if the local ring of `W` at the generic point of a component of a
proper intersection is Cohen–Macaulay, then its local intersection multiplicity is the
ambient-stalk length of the local ring of `W` modulo a generating regular sequence. -/
@[stacks 0B06] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.intersectionMultiplicity_eq_length_quotient_of_cohenMacaulay :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
      [Scheme.Regular X.left] (V W : X.left.IdealSheafData)
      [IsIntegral V.subscheme] [IsIntegral W.subscheme],
      Closeds.IntersectProperly V.support W.support →
      ∀ (Z : irreducibleComponents (V ⊔ W).subscheme) (c : ℕ)
        [hW : CohenMacaulayRing
          (stalk W.subscheme.presheaf
            ((Scheme.IdealSheafData.inclusion (le_sup_right : W ≤ V ⊔ W)).base
              (genericPoints.ofComponent Z).1) : CommRingCat)],
        let Y := X.left
        let ξ := genericPoints.ofComponent Z
        let x := (V ⊔ W).subschemeι ξ.1
        let R := Y.presheaf.stalk x
        let I := RingedSpace.idealSheafStalkIdeal
          (LocallyRingedSpace.closedImmersionIdealSubobject V.subschemeι.toLRSHom) x
        let J := RingedSpace.idealSheafStalkIdeal
          (LocallyRingedSpace.closedImmersionIdealSubobject W.subschemeι.toLRSHom) x
        let M := R ⧸ J
        ∀ (f : Fin c → R),
          RingTheory.Sequence.IsRegular R (List.ofFn f) →
          Ideal.span (Set.range f) = I →
          V.intersectionMultiplicity W ξ =
            ((Module.length R (M ⧸ (I • ⊤ : Submodule R M))).toNat : ℤ))
