/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PresheafedSpace.Sections.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AffineOpenPair
import Mathlib.Tactic.CrossRefAttribute

/-!
# Section comparisons over a common affine target

This file combines the explicit common-target data for a pair of affine opens with the generic
presheafed-space pushout comparison. The comparison itself remains owned by the generic sections
library; this leaf only packages its scheme-specific inputs.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.CommonAffineTarget

variable {X S : Scheme.{u}} {f : X ⟶ S} {U V : X.affineOpens}

/-- The relative section-ring comparison determined by explicit common-affine-target data. -/
@[stacks 01KP "relative sections comparison over a common affine target"]
noncomputable abbrev sectionsComparison
    (W : f.CommonAffineTarget U V) :=
  f.sectionPushoutToIntersection U V W.target W.left_le W.right_le

/-- The bundled relative comparison is surjective exactly when the absolute tensor comparison
is surjective. -/
@[stacks 01KP "relative and absolute section comparison surjectivity"]
theorem sectionsComparison_surjective_iff
    (W : f.CommonAffineTarget U V) :
    Function.Surjective (W.sectionsComparison).hom ↔
      Function.Surjective (X.sectionTensorToIntersection U V).hom := sorry

end AlgebraicGeometry.Scheme.Hom.CommonAffineTarget
