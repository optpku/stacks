/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData.Canonical

/-!
# Fpqc descent of quasi-coherent modules on algebraic spaces

Quasi-coherent modules on algebraic spaces satisfy effective descent along
fpqc covering families. The canonical restriction functor to descent data is fully faithful.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
variable {family : ι → Over X}

namespace DescentData

/-- Every quasi-coherent descent datum along an fpqc covering family of algebraic
spaces is effective. -/
theorem isEffective_of_fpqcCovering (hfamily : AlgebraicSpace.FpqcCovering family)
    (D : DescentData (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :
    D.IsEffective := sorry

end DescentData

namespace canonicalFunctor

/-- The canonical functor from quasi-coherent modules to descent data along an
fpqc covering family of algebraic spaces is fully faithful. -/
theorem fullyFaithful_of_fpqcCovering (hfamily : AlgebraicSpace.FpqcCovering family) :
    Nonempty
      (canonicalFunctor (fun i ↦ (family i).left) (fun i ↦ (family i).hom)).FullyFaithful := sorry

end canonicalFunctor

end AlgebraicGeometry.AlgebraicSpace.QCoh
