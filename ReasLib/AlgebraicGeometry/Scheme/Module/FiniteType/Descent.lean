module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration

/-!
# Descent of finite type scheme modules

Finite type for quasi-coherent scheme modules descends along fpqc covering families.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Modules.IsFiniteType

/-- A quasi-coherent scheme module whose pullbacks along an fpqc covering family are finite type
is itself finite type. -/
theorem of_fpqcCovering {X : Scheme.{u}} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : Scheme.FpqcCovering family)
    (hpullback : ∀ i : ι, ((Scheme.Modules.pullback (family i).hom).obj ℱ).IsFiniteType) :
    ℱ.IsFiniteType := sorry

end AlgebraicGeometry.Scheme.Modules.IsFiniteType
