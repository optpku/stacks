/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.CochainComplex
open CochainComplex.HomComplex
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- 20.41.0.1 (0A8L): the cohomology of the internal Hom complex on an open subspace is
identified with morphisms into a shift in the homotopy category.  The reusable owner is the
category-independent additive equivalence `CochainComplex.HomComplex.homologyHomAddEquiv`; the
open-subspace module category is only its source-facing specialization. -/

@[stacks 0A8L "Hom-complex cohomology and shifted homotopy morphisms"]
#check @CochainComplex.HomComplex.homologyHomAddEquiv

variable {X : RingedSpace.{u}} {U : Opens X.carrier}

@[stacks 0A8L "open-subspace specialization"]
#check
  @CochainComplex.HomComplex.homologyHomAddEquiv
    (openSubspaceModuleCategory X U)

/- The data-side owner is proof-audited here so downstream files can import this item without
reconstructing the composite from its two historical factors. -/
#print axioms CochainComplex.HomComplex.homologyHomAddEquiv

end AlgebraicGeometry.RingedSpace
