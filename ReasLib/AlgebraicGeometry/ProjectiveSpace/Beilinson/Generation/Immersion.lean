module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Conservative

/-!
# Beilinson generators on immersed schemes

Pulling the derived Beilinson generator back along a quasi-compact immersion gives a weak
generator on the source.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The pullback of the derived Beilinson generator along a quasi-compact immersion into
projective space weakly generates derived modules with quasicoherent cohomology on the source. -/
theorem pullbackDerivedBeilinsonGenerator_isWeakGenerator
    (A : Type u) [CommRing A] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ scheme A n) [QuasiCompact i] [IsImmersion i] :
    IsWeakGenerator
      ((Scheme.DerivedQCoh.pullback i).obj (derivedBeilinsonGenerator A n)) := sorry

end AlgebraicGeometry.ProjectiveSpace
