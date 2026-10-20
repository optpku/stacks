module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Locus

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat, locally finitely presented morphism admits open pieces of each relative
dimension whose union is dense in every fibre. -/
theorem exists_open_relativeDimension_decomposition {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    ∃ U : ℕ → X.Opens,
      (∀ s : S, Dense ((f.fiberι s) ⁻¹' (iSup U : X.Opens))) ∧
        ∀ d : ℕ, RelativeDimension ((U d).ι ≫ f) d := sorry

end AlgebraicGeometry.Scheme.Hom
