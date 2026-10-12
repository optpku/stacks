/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap87.Definition_87_25_1_Surjective

/-!
# Completion of a formal algebraic space along a closed subset of the reduction

The completion `completionAlong X T` of a formal algebraic space `X` along a
closed subset `T ⊆ Points (reduction X)` is the subfunctor of `X` classifying
morphisms from schemes over `S` whose induced map on reductions lands in `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace (Points ofOver ofOverMap)

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The algebraic space `ofOver (Over.reduction U)` is reduced in the
étale-local sense. -/
theorem ofOver_reduction_isReduced {S : Scheme.{u}} (U : Over S) :
    AlgebraicSpace.hasEtaleLocal (IsReduced : ObjectProperty Scheme.{u})
      (ofOver (AlgebraicGeometry.Over.reduction U)) :=
  sorry

/-- The morphism of reductions induced by a Yoneda section `g : yoneda.obj U ⟶ X`,
as the unique factor of `ofOverMap (Over.reductionι U) ≫ g` through
`reductionι X`. -/
def reductionMapFromOver {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [RX : Reduction X] {U : Over S}
    (g : yoneda.obj U ⟶ X) :
    ofOver (AlgebraicGeometry.Over.reduction U) ⟶ reduction X :=
  Classical.choose <|
    RX.liftUnique (ofOver_reduction_isReduced U)
      (ofOverMap (AlgebraicGeometry.Over.reductionι U) ≫ g)

/-- `reductionMapFromOver g` factors `ofOverMap (Over.reductionι U) ≫ g`
through the reduction morphism of `X`. -/
theorem reductionMapFromOver_spec {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] {U : Over S}
    (g : yoneda.obj U ⟶ X) :
    NatTrans.vcomp (reductionMapFromOver g) (reductionι X) =
      NatTrans.vcomp (ofOverMap (AlgebraicGeometry.Over.reductionι U)) g :=
  sorry

/-- A Yoneda section of `X` maps into `T` when the induced map of reductions
sends the points of `U_red` into `T`. -/
def mapsInto {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Set (Points (reduction X))) {U : Over S} (x : X.obj (op U)) : Prop :=
  Set.range (Points.map (reductionMapFromOver (yonedaEquiv.symm x))) ⊆ T

/-- `mapsInto T x` means that the image of `|U_red|` under the induced reduction of
the morphism classified by `x` is contained in `T`. -/
theorem mapsInto_iff {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Set (Points (reduction X))) {U : Over S} (x : X.obj (op U)) :
    mapsInto T x ↔
      Set.range (Points.map (reductionMapFromOver (yonedaEquiv.symm x))) ⊆ T :=
  sorry

/-- `mapsInto` is stable under precomposition with a morphism of schemes over `S`. -/
theorem mapsInto_map {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] {T : Set (Points (reduction X))}
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) {x : X.obj U}
    (hx : mapsInto T x) : mapsInto T (X.map φ x) :=
  sorry

/-- The map on points induced by `mapReduction f` is continuous for the
canonical topology on `Points`. -/
theorem continuous_mapReduction {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
    [Reduction X'] [Reduction X] (f : X' ⟶ X) :
    Continuous (Points.map (mapReduction f)) :=
  sorry

/-- If a section of `X'` maps into the closed preimage of `T` along `f : X' ⟶ X`,
then the postcomposition with `f` maps into `T`. -/
theorem mapsInto_comp {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
    [Reduction X'] [Reduction X] (f : X' ⟶ X)
    (T : Closeds (Points (reduction X))) {U : Over S} {x : X'.obj (op U)}
    (hx : mapsInto
      (T.preimage (Points.continuous_map (mapReduction f)) :
        Set (Points (reduction X'))) x) :
    mapsInto (T : Set (Points (reduction X))) (f.app (op U) x) :=
  sorry

/-- A section of `X'` maps into the closed preimage of `T` along `|f_red|` if and
only if the postcomposition with `f` maps into `T`. -/
theorem mapsInto_preimage_iff {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
    [Reduction X'] [Reduction X] (f : X' ⟶ X)
    (T : Closeds (Points (reduction X))) {U : Over S} {x : X'.obj (op U)} :
    mapsInto
        (T.preimage (Points.continuous_map (mapReduction f)) :
          Set (Points (reduction X'))) x ↔
      mapsInto (T : Set (Points (reduction X))) (f.app (op U) x) :=
  sorry

/-- The completion of a formal algebraic space `X` along a closed subset
`T ⊆ Points (reduction X)`, as the subfunctor of `X` classifying morphisms from
schemes whose induced map of reductions lands in `T`. -/
def completionAlong {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) : (Over S)ᵒᵖ ⥤ Type u where
  obj U := { x : X.obj U // mapsInto (T : Set (Points (reduction X))) x }
  map φ := ofHom fun x ↦ ⟨X.map φ x.1, mapsInto_map φ x.2⟩
  map_id := sorry
  map_comp := sorry

/-- Sections of `completionAlong X T` over `U` are the sections of `X` over `U`
that map into `T`. -/
theorem completionAlong_obj {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) (U : (Over S)ᵒᵖ) :
    (completionAlong X T).obj U =
      { x : X.obj U // mapsInto (T : Set (Points (reduction X))) x } :=
  sorry

/-- The completion of a formal algebraic space along a closed subset of the
reduction is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) :
    IsFormalAlgebraicSpace (completionAlong X T) :=
  sorry

namespace completionAlong

/-- The canonical morphism `completionAlong X T ⟶ X` from the completion along
`T`. -/
def ι {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) : completionAlong X T ⟶ X where
  app _ := ofHom fun x ↦ x.1
  naturality := sorry

/-- Components of `ι X T` are the subtype projections of `completionAlong X T`. -/
theorem ι_app {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) (U : (Over S)ᵒᵖ) :
    (ι X T).app U = ofHom fun x ↦ x.1 :=
  sorry

/-- A Yoneda section of `X` maps into `T` if and only if it lifts uniquely through
`ι X T`. -/
theorem exists_lift {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) {U : Over S} (x : X.obj (op U)) :
    mapsInto (T : Set (Points (reduction X))) x ↔
      ∃! y, (ι X T).app (op U) y = x :=
  sorry

/-- The morphism of completions induced by `f : X' ⟶ X`, landing in the closed
preimage `T.preimage (Points.continuous_map (mapReduction f))`. -/
def map {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
    [Reduction X'] [Reduction X] (f : X' ⟶ X)
    (T : Closeds (Points (reduction X))) :
    completionAlong X' (T.preimage (Points.continuous_map (mapReduction f))) ⟶
      completionAlong X T where
  app U := ofHom fun x ↦ ⟨f.app U x.1, mapsInto_comp f T x.2⟩
  naturality := sorry

/-- The underlying section of `map f T` is the component of `f`. -/
theorem map_app {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
    [Reduction X'] [Reduction X] (f : X' ⟶ X)
    (T : Closeds (Points (reduction X))) (U : (Over S)ᵒᵖ)
    (x : (completionAlong X'
      (T.preimage (Points.continuous_map (mapReduction f)))).obj U) :
    (ι X T).app U ((map f T).app U x) =
      f.app U
        ((ι X' (T.preimage (Points.continuous_map (mapReduction f)))).app U x) :=
  sorry

/-- The square of completions along a closed subset and its preimage commutes. -/
theorem map_comp_ι {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
    [Reduction X'] [Reduction X] (f : X' ⟶ X)
    (T : Closeds (Points (reduction X))) :
    map f T ≫ ι X T =
      ι X' (T.preimage (Points.continuous_map (mapReduction f))) ≫ f :=
  sorry

end completionAlong

end AlgebraicGeometry.FormalAlgebraicSpace
