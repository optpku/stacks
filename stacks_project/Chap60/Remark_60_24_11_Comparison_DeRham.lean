/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.DeRham.Terms

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineSmoothLiftTerms
export AlgebraicGeometry.Scheme.Modules.DeRham (oneForms forms term oneFormTensor asBaseSheaf baseTerm)
end CrystallineSmoothLiftTerms
variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
#check (AlgebraicGeometry.Scheme.Modules.DeRham.oneForms f : Y.Modules)
