module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.CurveDegree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.Normal.Local

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.IsModification

/-- On a normal modification of the spectrum of a two-dimensional Noetherian normal local
ring, a nonempty effective Cartier divisor supported in the closed fibre contains an
irreducible component of that fibre on which its conormal sheaf has strictly positive degree.
The conormal restriction is represented by the pullback of the divisor's ideal sheaf. -/
theorem existsComponent_conormalDegree_pos
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [_root_.IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsModification f] (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A)))
    (hX : X.isNormal) (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hD_nonempty : Nonempty D.subscheme)
    (hD_fiber : (D.support : Set X) ⊆ Set.range (f.fiberι (IsLocalRing.closedPoint A))) :
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
                  f.fiberι (IsLocalRing.closedPoint A))).obj D.negSheaf) inferInstance := sorry

end AlgebraicGeometry.IsModification
