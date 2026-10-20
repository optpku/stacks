/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Cover
public import ReasLib.Algebra.Homology.DifferentialGradedModule.QuasiIso

/-!
# Property P resolutions
-/

@[expose] public section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.PropertyP

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- A property P resolution of `M` is a specified quasi-isomorphism from a specified property P
right DG module. -/
@[stacks 09KP "property-P resolutions"]
structure Resolution (M : DifferentialGradedModule.{u, v} A) where
  /-- The resolving right DG module. -/
  obj : DifferentialGradedModule.{u, v} A
  /-- The comparison map from the resolving module to the target. -/
  π : obj ⟶ M
  /-- A chosen property P filtration of the resolving module. -/
  filtration : Filtration A obj
  /-- The comparison map is a quasi-isomorphism. -/
  quasiIso_π : quasiIso A ((toK A).map π)

namespace Resolution

/-- The resolving object of a property P resolution has property P. -/
@[stacks 09KP "property P of a resolution object"]
theorem propertyP_obj {M : DifferentialGradedModule.{u, v} A} (P : Resolution A M) :
    HasPropertyP A P.obj := sorry

/-- Lemma 22.20.4 (09KP): every right DG `A`-module admits a property P resolution. -/
@[stacks 09KP]
theorem nonempty (M : DifferentialGradedModule.{u, v} A) : Nonempty (Resolution A M) := sorry

end Resolution

end DifferentialGradedModule.PropertyP
