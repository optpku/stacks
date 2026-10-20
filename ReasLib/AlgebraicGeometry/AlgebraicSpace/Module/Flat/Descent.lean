module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc

/-!
# Fpqc descent of flat modules on algebraic spaces

Flatness of quasi-coherent modules on algebraic spaces descends along fpqc
covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IsFlat

/-- A quasi-coherent module on an algebraic space is flat if its pullbacks along an
fpqc covering family are flat. -/
theorem of_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (F : X.Modules) [F.IsQuasicoherent] (family : ι → Over X)
    (hfamily : FpqcCovering family)
    (hpullback : ∀ i, IsFlat ((pullback (family i).hom).obj F)) :
    IsFlat F := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IsFlat
