/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_6_5_NormalCone
public import stacks_project.Chap76.«76_6_1_2_Comparison»

/-!
# The normal cone as a closed subspace of the normal bundle

The canonical surjection from the symmetric algebra of the conormal sheaf to the total
conormal algebra induces a morphism of relative spectra `C_{Z/X} ⟶ N_{Z/X}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The canonical morphism from the normal cone of an immersion to its normal bundle. -/
noncomputable def normalConeToNormalBundle : normalCone i ⟶ normalBundle i :=
  relativeSpecMap (ConormalAlgebra.symmetricToTotal i)

/-- The comparison morphism is the relative spectrum of the symmetric-to-total conormal algebra
map. -/
theorem normalConeToNormalBundle_eq :
    normalConeToNormalBundle i =
      relativeSpecMap (ConormalAlgebra.symmetricToTotal i) :=
  rfl

/-- The canonical morphism from the normal cone to the normal bundle lies over the source of
the immersion. -/
theorem normalConeToNormalBundle_over :
    normalConeToNormalBundle i ≫ normalBundleπ i = normalConeπ i :=
  sorry

/-- The canonical morphism from the normal cone to the normal bundle is a closed immersion. -/
instance instIsClosedImmersion_normalConeToNormalBundle :
    IsClosedImmersion (normalConeToNormalBundle i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
