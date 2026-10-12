/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# The coordinate cover of punctured affine space

The coordinate basic opens and their cover belong to punctured affine space itself. Projective
maps and matrix-row constructions can therefore share this owner without depending on one
another.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace

variable (ι : Type u) (k : Type u) [CommRing k]

/-- The `i`-th affine coordinate restricted to punctured affine space. -/
@[stacks 01KX "coordinate on punctured affine space"]
noncomputable abbrev coordinateOnPuncture (i : ι) :
    Γ((puncturedOpen ι k).toScheme, ⊤) :=
  Scheme.Γ.map (puncturedOpen ι k).ι.op (coordinateSection ι k i)

/-- The punctured-affine global-sections comparison sends each polynomial coordinate to its
restriction on the punctured open. -/
@[simp, stacks 01KX "coordinate under the punctured-affine sections comparison"]
theorem globalSectionsComparison_coordinate (i : ι) :
    globalSectionsComparison ι k (coordinate ι k i) =
      coordinateOnPuncture ι k i := sorry

/-- The basic open of punctured affine space on which coordinate `i` is invertible. -/
@[stacks 01KX "coordinate open of punctured affine space"]
abbrev coordinateOpen (i : ι) : ((puncturedOpen ι k).toScheme).Opens :=
  (puncturedOpen ι k).toScheme.basicOpen (coordinateOnPuncture ι k i)

/-- Every coordinate open of punctured affine space is affine. -/
@[stacks 01KX "affine coordinate open of punctured affine space"]
theorem coordinateOpen_isAffineOpen (i : ι) :
    IsAffineOpen (coordinateOpen ι k i) := sorry

/-- The coordinate basic opens cover punctured affine space. -/
@[stacks 01KX "coordinate opens cover punctured affine space"]
theorem coordinateOpen_isOpenCover :
    TopologicalSpace.IsOpenCover (coordinateOpen ι k) := sorry

/-- The standard coordinate open cover of punctured affine space. -/
@[stacks 01KX "punctured affine coordinate cover"]
noncomputable def coordinateOpenCover : (puncturedOpen ι k).toScheme.OpenCover :=
  Scheme.openCoverOfIsOpenCover _ (coordinateOpen ι k) (coordinateOpen_isOpenCover ι k)

end AlgebraicGeometry.PuncturedAffineSpace
