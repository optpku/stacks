module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Completion of formal algebraic spaces along closed subsets

Completion consists of sections whose reduced source maps into a prescribed
closed subset of the reduction. It commutes with inverse images under morphisms.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace (Points ofOver ofOverMap)

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Recompletion

variable {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
  [IsFormalAlgebraicSpace X] (R : ReductionData X)

/-- A scheme-valued section induces the canonical morphism from its reduced source
to the reduction of the target. -/
def reductionMapFromOver {U : Over S} (g : yoneda.obj U ⟶ X) :
    ofOver (AlgebraicGeometry.Over.reduction U) ⟶ R.space :=
  R.mapFromReduced
    (AlgebraicSpace.existsSurjectiveEtale.of
      (𝟙 (ofOver (AlgebraicGeometry.Over.reduction U)))
      (AlgebraicSpace.ofOver_id_presheaf_etale _)
      (AlgebraicSpace.ofOver_id_locallySurjective _)
      (Scheme.instIsReducedReduction U.left))
    (ofOverMap (AlgebraicGeometry.Over.reductionι U) ≫ g)

/-- The induced morphism from the reduced source factors the original section
restricted along the reduction inclusion. -/
theorem reductionMapFromOver_spec {U : Over S} (g : yoneda.obj U ⟶ X) :
    NatTrans.vcomp (reductionMapFromOver R g) R.ι =
      NatTrans.vcomp (ofOverMap (AlgebraicGeometry.Over.reductionι U)) g :=
  (R.mapFromReduced_spec _ _).1

/-- A section maps into a subset when the image of its reduced source is contained
in that subset of the target reduction. -/
def mapsInto (T : Set (Points R.space)) {U : Over S} (x : X.obj (op U)) : Prop :=
  Set.range (Points.map (reductionMapFromOver R (yonedaEquiv.symm x))) ⊆ T

/-- The section membership predicate is precisely containment of the image of the
canonical morphism from the reduced source. -/
theorem mapsInto_iff (T : Set (Points R.space)) {U : Over S} (x : X.obj (op U)) :
    mapsInto R T x ↔
      Set.range (Points.map (reductionMapFromOver R (yonedaEquiv.symm x))) ⊆ T :=
  Iff.rfl

/-- Containment of the reduced image is stable under restriction along a morphism
of schemes over the base. -/
theorem mapsInto_map {T : Set (Points R.space)}
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) {x : X.obj U}
    (hx : mapsInto R T x) : mapsInto R T (X.map φ x) :=
  sorry

/-- A section maps into the inverse image of a closed subset of the target
reduction exactly when its postcomposition maps into that closed subset. -/
theorem mapsInto_preimage_iff {X' : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] (R' : ReductionData X') (f : X' ⟶ X)
    (T : Closeds (Points R.space)) {U : Over S} {x : X'.obj (op U)} :
    mapsInto R'
        (T.preimage (Points.continuous_map (R'.map R f)) : Set (Points R'.space)) x ↔
      mapsInto R (T : Set (Points R.space)) (f.app (op U) x) :=
  sorry

/-- Completion along a closed subset of the reduction is the subfunctor of sections
whose reduced source has image in that subset. -/
def functor (T : Closeds (Points R.space)) : (Over S)ᵒᵖ ⥤ Type u where
  obj U := { x : X.obj U // mapsInto R (T : Set (Points R.space)) x }
  map φ := ofHom fun x ↦ ⟨X.map φ x.1, mapsInto_map R φ x.2⟩
  map_id U := by
    ext x
    exact congrArg (fun k ↦ k x.1) (X.map_id U)
  map_comp φ ψ := by
    ext x
    exact congrArg (fun k ↦ k x.1) (X.map_comp φ ψ)

/-- Sections of the completion are the sections whose reduced image is contained
in the specified closed subset. -/
theorem functor_obj (T : Closeds (Points R.space)) (U : (Over S)ᵒᵖ) :
    (functor R T).obj U = { x : X.obj U // mapsInto R (T : Set (Points R.space)) x } :=
  rfl

/-- Completion along a closed subset of the reduction is a formal algebraic space. -/
@[stacks 0GVR]
theorem isFormalAlgebraicSpace (T : Closeds (Points R.space)) :
    IsFormalAlgebraicSpace (functor R T) :=
  sorry

/-- The canonical morphism from the completion to its ambient formal algebraic
space is the inclusion of sections. -/
def ι (T : Closeds (Points R.space)) : functor R T ⟶ X where
  app _ := ofHom fun x ↦ x.1
  naturality := fun {_ _} _ ↦ rfl

/-- The components of the completion inclusion are subtype projections. -/
theorem ι_app (T : Closeds (Points R.space)) (U : (Over S)ᵒᵖ) :
    (ι R T).app U = ofHom fun x ↦ x.1 :=
  rfl

/-- A section has reduced image in the closed subset exactly when it lifts uniquely
to the completion. -/
theorem exists_lift (T : Closeds (Points R.space)) {U : Over S} (x : X.obj (op U)) :
    mapsInto R (T : Set (Points R.space)) x ↔
      ∃! y, (ι R T).app (op U) y = x := by
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl, fun y hy ↦ Subtype.ext hy⟩
  · rintro ⟨y, hy, _⟩
    exact hy ▸ y.2

variable {X' : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X']

/-- A morphism induces a morphism from the completion along the inverse image
of a closed subset to the completion along that subset. -/
def map (R' : ReductionData X') (R : ReductionData X) (f : X' ⟶ X) (T : Closeds (Points R.space)) :
    functor R' (T.preimage (Points.continuous_map (R'.map R f))) ⟶ functor R T where
  app U := ofHom fun x ↦
    ⟨f.app U x.1, (mapsInto_preimage_iff R R' f T).mp x.2⟩
  naturality := by
    intro U V φ
    ext x
    apply Subtype.ext
    exact congrArg (fun k ↦ k x.1) (f.naturality φ)

/-- The induced morphism of completions applies the original morphism to the
underlying section. -/
theorem map_app (R' : ReductionData X') (f : X' ⟶ X)
    (T : Closeds (Points R.space)) (U : (Over S)ᵒᵖ)
    (x : (functor R' (T.preimage (Points.continuous_map (R'.map R f)))).obj U) :
    (ι R T).app U ((map R' R f T).app U x) =
      f.app U ((ι R' (T.preimage (Points.continuous_map (R'.map R f)))).app U x) :=
  rfl

/-- The induced morphism of completions commutes with the canonical inclusions. -/
theorem map_comp_ι (R' : ReductionData X') (f : X' ⟶ X)
    (T : Closeds (Points R.space)) :
    map R' R f T ≫ ι R T =
      ι R' (T.preimage (Points.continuous_map (R'.map R f))) ≫ f :=
  rfl

end Recompletion

/-- Completion along a closed subset of a reduction commutes with pullback along
a morphism of formal algebraic spaces. -/
@[stacks 0GVT]
theorem completionAlong_isPullback {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
    (R' : ReductionData X') (R : ReductionData X) (f : X' ⟶ X)
    (T : Closeds (Points R.space)) :
    IsPullback
      (Recompletion.ι R' (T.preimage (Points.continuous_map (R'.map R f))))
      (Recompletion.map R' R f T) f (Recompletion.ι R T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
