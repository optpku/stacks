/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.TFAE

/-!
# Descent of finite locally free scheme modules

Finite local freeness for quasi-coherent scheme modules descends along fpqc covering families.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree

/-- A quasi-coherent scheme module whose pullbacks along an fpqc covering family are finite
locally free is itself finite locally free. -/
theorem of_fpqcCovering {X : Scheme.{u}} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : Scheme.FpqcCovering family)
    (hpullback : ∀ i : ι,
      ((Scheme.Modules.pullback (family i).hom).obj ℱ).IsFiniteLocallyFree) :
    ℱ.IsFiniteLocallyFree := sorry

end AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree
