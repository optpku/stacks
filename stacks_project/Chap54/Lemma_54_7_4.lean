/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.ConormalDegree

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 54.7.4: in Situation 54.7.1, if `X` is normal and a nonempty effective
Cartier divisor `D` is set-theoretically contained in the special fibre, then some
irreducible component `C i` is contained in `D` and the restriction of the conormal
sheaf, represented by the pullback of the ideal sheaf `D.negSheaf`, has positive degree. -/
@[stacks 0AXA] #check
(AlgebraicGeometry.IsModification.existsComponent_conormalDegree_pos :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [_root_.IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsModification f] (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A)))
    (hX : X.isNormal) (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hD_nonempty : Nonempty D.subscheme)
    (hD_fiber : (D.support : Set X) ⊆ Set.range (f.fiberι (IsLocalRing.closedPoint A))),
    ∃ i : Fin r,
      Set.range
          ((f.fiber (IsLocalRing.closedPoint A)).irreducibleComponentSubschemeι (C i) ≫
            f.fiberι (IsLocalRing.closedPoint A)) ⊆ (D.support : Set X) ∧
        ∃ hCiProper :
            IsProper
              ((f.fiber (IsLocalRing.closedPoint A)).irreducibleComponentSubschemeι (C i) ≫
                f.fiberToSpecResidueField (IsLocalRing.closedPoint A)),
          ∃ hCi : topologicalKrullDim
              ((f.fiber (IsLocalRing.closedPoint A)).irreducibleComponentSubscheme (C i)) = 1,
            0 < @Scheme.Modules.curveDegreeOfInvertible _ _ _
              ((f.fiber (IsLocalRing.closedPoint A)).irreducibleComponentSubschemeι (C i) ≫
                f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
              hCiProper hCi.le
              ((Scheme.Modules.pullback
                ((f.fiber (IsLocalRing.closedPoint A)).irreducibleComponentSubschemeι (C i) ≫
                  f.fiberι (IsLocalRing.closedPoint A))).obj D.negSheaf) inferInstance)
