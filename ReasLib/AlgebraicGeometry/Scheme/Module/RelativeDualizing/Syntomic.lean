module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

/-- A relative dualizing sheaf for a locally quasi-finite syntomic morphism between locally
Noetherian schemes is an invertible scheme module. -/
theorem invertibleOfLocallyQuasiFiniteSyntomic
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyQuasiFinite f] [Syntomic f] (W : f.RelativeDualizingSheaf) :
    Scheme.Modules.Invertible W.module.obj := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
