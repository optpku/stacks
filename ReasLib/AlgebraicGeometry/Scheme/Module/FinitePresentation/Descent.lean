module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation

/-!
# Descent of finite presentation for scheme modules

Finite presentation for quasi-coherent scheme modules descends along fpqc covering families.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Modules.IsFinitePresentation

/-- A quasi-coherent scheme module whose pullbacks along an fpqc covering family are finitely
presented is itself finitely presented. -/
theorem of_fpqcCovering {X : Scheme.{u}} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : Scheme.FpqcCovering family)
    (hpullback : ∀ i : ι,
      ((Scheme.Modules.pullback (family i).hom).obj ℱ).IsFinitePresentation) :
    ℱ.IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.Modules.IsFinitePresentation
