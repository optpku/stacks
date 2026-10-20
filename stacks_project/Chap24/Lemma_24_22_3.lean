/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Triangulated
import StacksCheckRecall

/-!
# Lemma 24.22.3

Axiom `(C)` is represented intrinsically by the canonical mapping-cone triangle of every closed
degree-zero DG-module morphism. The reusable owner constructs the cone, its two structural maps,
the underlying cochain-complex comparison, and the induced triangle in the DG homotopy category.
-/

@[expose] public section

open SheafOfModules.RingedSite.DifferentialGradedModule

/- Lemma 24.22.3 (0FS6): every DG-module morphism has its canonical mapping-cone triangle. -/
@[stacks 0FS6] #check @MappingCone.triangleK

/- The module-level triangle has the source morphism, the canonical cone inclusion, and the
projection to the shifted source as its three arrows. -/
#check @MappingCone.triangle
#check @MappingCone.inr
#check @MappingCone.toShift

/- Its underlying cochain-complex triangle is the standard Mathlib mapping-cone triangle. -/
@[stacks 0FS6 "underlying mapping-cone triangle"]
#check @MappingCone.underlyingTriangleIso

/- The third arrow in the homotopy category is the cone projection followed by the canonical
shift comparison, which is the formal counterpart of the boundary calculation in the source. -/
@[stacks 0FS6 "boundary is the shifted defining morphism"]
#check @MappingCone.triangleK_mor₃

/- These cone triangles supply the intrinsic pretriangulated structure used downstream. -/
#check @Homotopy.pretriangulated
