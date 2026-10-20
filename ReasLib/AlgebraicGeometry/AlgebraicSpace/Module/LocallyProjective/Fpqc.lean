/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsLocallyProjective

/-- A quasi-coherent module on an algebraic space over a scheme is locally projective
if its pullbacks along an fpqc covering family are locally projective. -/
@[stacks 060Y]
theorem of_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : FpqcCovering family)
    (hpullback : ∀ i, IsLocallyProjective ((Modules.pullback (family i).hom).obj ℱ)) :
    IsLocallyProjective ℱ := sorry

end IsLocallyProjective
end AlgebraicGeometry.AlgebraicSpace.Modules
