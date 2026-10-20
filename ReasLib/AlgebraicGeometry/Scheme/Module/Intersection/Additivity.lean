/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic.MultiTwist

/-!
# Additivity of intersection numbers

This file records the additivity of a numerical intersection number when one invertible-module
factor is expressed as a tensor product.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- If one invertible-module factor is isomorphic to a tensor product, its intersection number
is the sum of the intersection numbers obtained from the two tensor factors. -/
theorem number_eq_add_of_iso_tensorObj
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (hZdim : topologicalKrullDim Z.subscheme = d)
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (i : Fin d) (L' L'' : X.Modules) [Invertible L'] [Invertible L'']
    (hTensor : L i ≅ tensorObj L' L'') :
    number k f Z hZdim L =
      number k f Z hZdim (Function.update L i L') +
        number k f Z hZdim (Function.update L i L'') := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
