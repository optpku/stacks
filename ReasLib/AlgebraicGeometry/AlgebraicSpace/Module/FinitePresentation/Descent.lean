module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsFinitePresentation

/-- A quasi-coherent module on an algebraic space over a scheme is of finite presentation
if its pullbacks along an fpqc covering family are of finite presentation. -/
@[stacks 060V]
theorem of_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : FpqcCovering family)
    (hpullback :
      ∀ i : ι, ((Modules.pullback (family i).hom).obj ℱ).IsFinitePresentation) :
    ℱ.IsFinitePresentation := sorry

end IsFinitePresentation
end AlgebraicGeometry.AlgebraicSpace.Modules
