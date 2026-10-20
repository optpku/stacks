module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.RingTheory.Normal.Local

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.IsModification

/-- For a non-isomorphic modification of a two-dimensional normal local base, one
nonzero maximal-ideal element admits compatible factorizations at exclusive closed
points of every reduced irreducible component of the closed fibre. -/
theorem existsNonzeroComponentFactorizations
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [_root_.IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsModification f] (h_noniso : ¬ IsIso f) (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) :
    ∃ f₀ ∈ IsLocalRing.maximalIdeal A, f₀ ≠ 0 ∧
      ∀ i, ∃ (x : f.fiber (IsLocalRing.closedPoint A))
          (hx : x ∈ (C i : Set (f.fiber (IsLocalRing.closedPoint A)))),
        x ∈ closedPoints (f.fiber (IsLocalRing.closedPoint A)) ∧
          (∀ j, j ≠ i → x ∉ (C j : Set (f.fiber (IsLocalRing.closedPoint A)))) ∧
          ∃ gᵢ fᵢ : X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint A) x),
            ((StructureSheaf.toStalk A (f (f.fiberι (IsLocalRing.closedPoint A) x)) ≫
                f.stalkMap (f.fiberι (IsLocalRing.closedPoint A) x)) f₀ = gᵢ * fᵢ) ∧
              gᵢ ∈ IsLocalRing.maximalIdeal
                (X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint A) x)) ∧
              ((f.fiberι (IsLocalRing.closedPoint A)).stalkMap x ≫
                  ((f.fiber (IsLocalRing.closedPoint A)).irreducibleComponentSubschemeι
                    (C i)).stalkMap ⟨x, hx⟩) gᵢ ≠ 0 := sorry

end AlgebraicGeometry.IsModification
