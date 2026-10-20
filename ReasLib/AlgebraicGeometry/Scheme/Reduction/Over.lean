module

public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Functor

/-!
# Reduction of schemes over a base

Relative reduction reuses the absolute construction and records the induced
structure map explicitly in the over category.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Over

/-- The reduction of a scheme over `S`, with its induced structure morphism. -/
@[stacks 0356 "relative reduction"]
noncomputable abbrev reduction {S : Scheme.{u}} (X : CategoryTheory.Over S) :
    CategoryTheory.Over S :=
  Over.mk (Scheme.reductionι X.left ≫ X.hom)

/-- The absolute reduction inclusion respects the relative structure morphism. -/
@[stacks 0356 "relative reduction inclusion structure map"]
theorem reductionι_w {S : Scheme.{u}} (X : CategoryTheory.Over S) :
    Scheme.reductionι X.left ≫ X.hom = (reduction X).hom := sorry

/-- The canonical inclusion of the relative reduction. -/
@[stacks 0356 "relative reduction inclusion"]
noncomputable abbrev reductionι {S : Scheme.{u}} (X : CategoryTheory.Over S) :
  reduction X ⟶ X :=
  Over.homMk (Scheme.reductionι X.left) (reductionι_w X)

/-- The relative reduction inclusion is an isomorphism when the underlying scheme is reduced. -/
@[stacks 0356 "relative reduction of a reduced scheme"]
theorem reductionι_isIso
    {S : Scheme.{u}} (X : CategoryTheory.Over S) [IsReduced X.left] :
    IsIso (reductionι X) := sorry

/-- The absolute reduction map induced by a relative morphism respects the structure maps. -/
@[stacks 0356 "relative reduction map structure equation"]
theorem reductionMap_w
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    Scheme.reductionMap f.left ≫ (reduction Y).hom = (reduction X).hom := sorry

/-- The canonical map on relative reductions. -/
@[stacks 0356 "relative map on reductions"]
noncomputable def reductionMap
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    reduction X ⟶ reduction Y :=
  Over.homMk (Scheme.reductionMap f.left) (reductionMap_w f)

/-- The underlying scheme map of a relative reduction map is the absolute reduction map. -/
@[simp, stacks 0356 "relative reduction map underlying equation"]
theorem reductionMap_left
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    (reductionMap f).left = Scheme.reductionMap f.left := sorry

/-- Relative reduction preserves identity morphisms. -/
@[simp, stacks 0356 "relative reduction map identity"]
theorem reductionMap_id {S : Scheme.{u}} (X : CategoryTheory.Over S) :
    reductionMap (𝟙 X) = 𝟙 (reduction X) := sorry

/-- Relative reduction preserves composition. -/
@[simp, stacks 0356 "relative reduction map composition"]
theorem reductionMap_comp
    {S : Scheme.{u}} {X Y Z : CategoryTheory.Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    reductionMap (f ≫ g) = reductionMap f ≫ reductionMap g := sorry

/-- Reduction as an endofunctor on schemes over a fixed base. -/
@[stacks 0356 "relative reduction functor"]
noncomputable def reductionFunctor (S : Scheme.{u}) :
    CategoryTheory.Over S ⥤ CategoryTheory.Over S where
  obj := reduction
  map := reductionMap
  map_id := reductionMap_id
  map_comp := reductionMap_comp

/-- The relative reduction functor acts on objects by `reduction`. -/
@[simp, stacks 0356 "relative reduction functor object"]
theorem reductionFunctor_obj
    {S : Scheme.{u}} (X : CategoryTheory.Over S) :
    (reductionFunctor S).obj X = reduction X := sorry

/-- The relative reduction functor acts on morphisms by `reductionMap`. -/
@[simp, stacks 0356 "relative reduction functor map"]
theorem reductionFunctor_map
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    (reductionFunctor S).map f = reductionMap f := sorry

/-- Naturality of the relative reduction inclusions. -/
@[stacks 0356 "relative reduction inclusion naturality"]
theorem reductionι_naturality
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    (reductionFunctor S).map f ≫ reductionι Y =
      reductionι X ≫ (𝟭 (CategoryTheory.Over S)).map f := sorry

/-- The relative reduction inclusions form a natural transformation to the identity. -/
@[stacks 0356 "relative reduction inclusion natural transformation"]
noncomputable def reductionιNatTrans (S : Scheme.{u}) :
    reductionFunctor S ⟶ 𝟭 (CategoryTheory.Over S) where
  app := reductionι
  naturality := fun {_ _} f ↦ reductionι_naturality f

/-- The component of the relative reduction-inclusion transformation is `reductionι`. -/
@[simp, stacks 0356 "relative reduction inclusion component"]
theorem reductionιNatTrans_app
    {S : Scheme.{u}} (X : CategoryTheory.Over S) :
    (reductionιNatTrans S).app X = reductionι X := sorry

namespace Hom

/-- The absolute reduction lift respects the relative structure maps. -/
@[stacks 0356 "relative reduction lift structure equation"]
theorem reductionLift_w
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S}
    [IsReduced X.left] (f : X ⟶ Y) :
    Scheme.Hom.reductionLift f.left ≫ (reduction Y).hom = X.hom := sorry

/-- The canonical relative factorization from a reduced source through the target reduction. -/
@[stacks 0356 "relative reduction lift"]
noncomputable def reductionLift
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S}
    [IsReduced X.left] (f : X ⟶ Y) : X ⟶ reduction Y :=
  Over.homMk (Scheme.Hom.reductionLift f.left) (reductionLift_w f)

/-- The relative reduction lift followed by the inclusion is the original morphism. -/
@[reassoc (attr := simp), stacks 0356 "relative reduction lift computation"]
theorem reductionLift_reductionι
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S}
    [IsReduced X.left] (f : X ⟶ Y) :
    reductionLift f ≫ reductionι Y = f := sorry

/-- Every relative factorization from a reduced source is the canonical reduction lift. -/
@[stacks 0356 "relative reduction lift uniqueness"]
theorem eq_reductionLift
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S}
    [IsReduced X.left] {f : X ⟶ Y} (g : X ⟶ reduction Y)
    (hg : g ≫ reductionι Y = f) :
    g = reductionLift f := sorry

/-- Lifting a relative morphism already landing in a reduction recovers it. -/
@[simp, stacks 0356 "relative reduction lift cancellation"]
theorem reductionLift_comp_reductionι
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S}
    [IsReduced X.left] (g : X ⟶ reduction Y) :
    reductionLift (g ≫ reductionι Y) = g := sorry

/-- Relative morphisms from a reduced source to `Y` are equivalent to relative morphisms to its
reduction. -/
@[stacks 0356 "relative reduction hom equivalence"]
noncomputable def reductionHomEquiv
    {S : Scheme.{u}} (X Y : CategoryTheory.Over S) [IsReduced X.left] :
    (X ⟶ reduction Y) ≃ (X ⟶ Y) where
  toFun g := g ≫ reductionι Y
  invFun := reductionLift
  left_inv := reductionLift_comp_reductionι
  right_inv := reductionLift_reductionι

/-- The forward relative reduction hom equivalence is postcomposition with the inclusion. -/
@[simp, stacks 0356 "relative reduction hom equivalence forward"]
theorem reductionHomEquiv_apply
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S} [IsReduced X.left]
    (g : X ⟶ reduction Y) :
    reductionHomEquiv X Y g = g ≫ reductionι Y := sorry

/-- The inverse relative reduction hom equivalence is the canonical lift. -/
@[simp, stacks 0356 "relative reduction hom equivalence inverse"]
theorem reductionHomEquiv_symm_apply
    {S : Scheme.{u}} {X Y : CategoryTheory.Over S} [IsReduced X.left]
    (f : X ⟶ Y) :
    (reductionHomEquiv X Y).symm f = reductionLift f := sorry

end Hom

end AlgebraicGeometry.Over
