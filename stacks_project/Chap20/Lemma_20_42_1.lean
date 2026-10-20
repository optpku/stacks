/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.RHom.Cohomology
open scoped CartesianClosed

/- Lemma 20.42.1 (08DK): for an open `U ⊆ X` and derived modules `L,M`, degree-zero open
cohomology of the derived internal Hom is canonically isomorphic to the morphism group between
their derived restrictions to `U`. -/
@[stacks 08DK "degree-zero local derived-Hom comparison"]
#check @openH0_isomorphic_restrictionHom

/- The representative-level companion is part of the same source-facing comparison API. -/
@[stacks 08DK "degree-zero local derived-Hom comparison for representatives"]
#check @openH0_isomorphic_representativeHom

end
