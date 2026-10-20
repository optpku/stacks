module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.TraceSection
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

/-- For a locally quasi-finite syntomic morphism of Noetherian schemes, the different of a
relative dualizing sheaf on a trace section equals the Kähler different of the morphism. -/
theorem different_eq_kaehlerDifferent {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [LocallyQuasiFinite f] [Syntomic f]
    (W : f.RelativeDualizingSheaf) (τ : W.module.obj.sections)
    (hτ : W.IsTraceSection τ) :
    W.different τ = f.kaehlerDifferent := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
