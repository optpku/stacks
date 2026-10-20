/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.SpecField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Geometric properties of the spectrum of a field

The spectrum of a field, represented as an algebraic space over itself, is
universally catenary and quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The spectrum of a field, viewed as an algebraic space over itself, is universally catenary. -/
instance instUniversallyCatenary_specField (k : Type u) [Field k] :
    UniversallyCatenary (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  @instUniversallyCatenary_ofOver _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (inferInstance : AlgebraicGeometry.UniversallyCatenary (Spec (CommRingCat.of k)))

/-- The spectrum of a field, viewed as an algebraic space over itself, is quasi-separated. -/
instance instIsQuasiSeparated_specField (k : Type u) [Field k] :
    IsQuasiSeparated (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  @instIsQuasiSeparated _ _
    (@instIsSeparated_ofOver _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))
      (inferInstance : AlgebraicGeometry.IsSeparated (𝟙 (Spec (CommRingCat.of k)))))

end AlgebraicGeometry.AlgebraicSpace
