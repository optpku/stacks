/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Reduction

/-!
# The reduction functor

Maps on reductions are built from Mathlib's explicit closed-subscheme map.
The universal property is exposed both as a canonical lift and a hom-set
equivalence.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace Hom

/-- A morphism from a reduced scheme kills the nilradical of its target. -/
@[stacks 0356 "reduced source kills the target nilradical"]
theorem nilradical_le_ker_of_isReduced
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
    Y.nilradical ≤ f.ker := sorry

/-- The kernel of the reduction inclusion is contained in the kernel of every morphism from a
reduced scheme. This is the closed-subscheme form of `nilradical_le_ker_of_isReduced`. -/
@[stacks 0356 "reduction inclusion kernel is killed by a reduced source"]
theorem reductionι_ker_le_ker_of_isReduced
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
    (reductionι Y).ker ≤ f.ker := sorry

end Hom

/-- A scheme morphism carries the target nilradical into the mapped source nilradical. -/
@[stacks 0356 "nilradical functoriality"]
theorem nilradical_le_map_nilradical {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.nilradical ≤ X.nilradical.map f := sorry

/-- The canonical morphism on reductions induced by a scheme morphism. -/
@[stacks 0356 "map on reductions"]
noncomputable def reductionMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    reduction X ⟶ reduction Y :=
  IdealSheafData.subschemeMap X.nilradical Y.nilradical f
    (nilradical_le_map_nilradical f)

/-- The map on reductions commutes with the reduction inclusions. -/
@[reassoc (attr := simp), stacks 0356 "map on reductions and inclusions"]
theorem reductionMap_reductionι {X Y : Scheme.{u}} (f : X ⟶ Y) :
    reductionMap f ≫ reductionι Y = reductionι X ≫ f := sorry

namespace Hom

/-- The canonical factorization of a morphism from a reduced scheme through the target
reduction. -/
@[stacks 0356 "reduction lift"]
noncomputable def reductionLift
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) : X ⟶ reduction Y :=
  Y.nilradical.lift f (Hom.nilradical_le_ker_of_isReduced f)

/-- The reduction lift followed by the reduction inclusion is the original morphism. -/
@[reassoc (attr := simp), stacks 0356 "reduction lift factorization"]
theorem reductionLift_reductionι
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
    reductionLift f ≫ reductionι Y = f := sorry

/-- Every factorization through a reduction is the canonical reduction lift. -/
@[stacks 0356 "reduction lift uniqueness"]
theorem eq_reductionLift
    {X Y : Scheme.{u}} [IsReduced X] {f : X ⟶ Y}
    (g : X ⟶ reduction Y) (hg : g ≫ reductionι Y = f) :
    g = reductionLift f := sorry

/-- Lifting a morphism already landing in a reduction recovers that morphism. -/
@[simp, stacks 0356 "reduction lift of a factored morphism"]
theorem reductionLift_comp_reductionι
    {X Y : Scheme.{u}} [IsReduced X] (g : X ⟶ reduction Y) :
    reductionLift (g ≫ reductionι Y) = g := sorry

/-- Morphisms from a reduced scheme to `Y` are equivalent to morphisms to `reduction Y`. -/
@[stacks 0356 "universal property of reduction"]
noncomputable def reductionHomEquiv (X Y : Scheme.{u}) [IsReduced X] :
    (X ⟶ reduction Y) ≃ (X ⟶ Y) where
  toFun g := g ≫ reductionι Y
  invFun := reductionLift
  left_inv := reductionLift_comp_reductionι
  right_inv := reductionLift_reductionι

/-- The forward reduction hom equivalence is postcomposition with the reduction inclusion. -/
@[simp, stacks 0356 "reduction hom equivalence forward map"]
theorem reductionHomEquiv_apply
    {X Y : Scheme.{u}} [IsReduced X] (g : X ⟶ reduction Y) :
    reductionHomEquiv X Y g = g ≫ reductionι Y := sorry

/-- The inverse reduction hom equivalence is the canonical reduction lift. -/
@[simp, stacks 0356 "reduction hom equivalence inverse map"]
theorem reductionHomEquiv_symm_apply
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
    (reductionHomEquiv X Y).symm f = reductionLift f := sorry

end Hom

/-- A morphism between reductions is canonical when it commutes with their inclusions. -/
@[stacks 0356 "map on reductions uniqueness"]
theorem eq_reductionMap_of_comp_reductionι
    {X Y : Scheme.{u}} {f : X ⟶ Y} {g : reduction X ⟶ reduction Y}
    (hg : g ≫ reductionι Y = reductionι X ≫ f) :
    g = reductionMap f := sorry

/-- Reduction sends identity morphisms to identity morphisms. -/
@[simp, stacks 0356 "reduction map identity"]
theorem reductionMap_id (X : Scheme.{u}) :
    reductionMap (𝟙 X) = 𝟙 (reduction X) := sorry

/-- Reduction preserves composition. -/
@[simp, stacks 0356 "reduction map composition"]
theorem reductionMap_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    reductionMap (f ≫ g) = reductionMap f ≫ reductionMap g := sorry

/-- Scheme-theoretic reduction as an endofunctor. -/
@[stacks 0356 "reduction functor"]
noncomputable def reductionFunctor : Scheme.{u} ⥤ Scheme.{u} where
  obj := reduction
  map := reductionMap
  map_id := reductionMap_id
  map_comp := reductionMap_comp

/-- The reduction functor acts on objects by the canonical reduction. -/
@[simp, stacks 0356 "reduction functor on objects"]
theorem reductionFunctor_obj (X : Scheme.{u}) :
    reductionFunctor.obj X = reduction X := sorry

/-- The reduction functor acts on morphisms by `reductionMap`. -/
@[simp, stacks 0356 "reduction functor on morphisms"]
theorem reductionFunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    reductionFunctor.map f = reductionMap f := sorry

/-- Naturality of the reduction inclusions. -/
@[stacks 0356 "naturality of reduction inclusions"]
theorem reductionι_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    reductionFunctor.map f ≫ reductionι Y =
      reductionι X ≫ (𝟭 Scheme.{u}).map f := sorry

/-- The reduction inclusions form a natural transformation from reduction to the identity. -/
@[stacks 0356 "reduction inclusion natural transformation"]
noncomputable def reductionιNatTrans : reductionFunctor ⟶ 𝟭 Scheme.{u} where
  app := reductionι
  naturality := fun {_ _} f ↦ reductionι_naturality f

/-- The component of the reduction-inclusion natural transformation is `reductionι`. -/
@[simp, stacks 0356 "reduction inclusion natural transformation component"]
theorem reductionιNatTrans_app (X : Scheme.{u}) :
    reductionιNatTrans.app X = reductionι X := sorry

end AlgebraicGeometry.Scheme
