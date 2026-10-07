module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Affine
public import ReasLib.RingTheory.Flat.FaithfullyFlat.Projective

/-!
# Fpqc descent of locally projective scheme modules
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry
namespace Scheme.Modules.IsLocallyProjective

/-- A quasi-coherent scheme module whose pullbacks along an fpqc covering family are locally
projective is itself locally projective. -/
@[stacks 05JZ]
theorem of_fpqcCovering {X : Scheme.{u}} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : Scheme.FpqcCovering family)
    (hpullback : ∀ i, IsLocallyProjective ((Scheme.Modules.pullback (family i).hom).obj ℱ)) :
    IsLocallyProjective ℱ := sorry

end Scheme.Modules.IsLocallyProjective
end AlgebraicGeometry
