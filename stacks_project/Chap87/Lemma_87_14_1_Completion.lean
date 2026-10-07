module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap87.Lemma_87_14_6

/-!
# Scheme-level completion along a closed subset

For a scheme `X` over `S` and a closed subset `T ⊆ |X|`, the completion along
`T` is the subfunctor of `yoneda.obj X` classifying morphisms of schemes over
`S` whose image of points lands in `T`. On `X = Spec(A)` this agrees with
`affineCompletionAlong`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace completionAlong

/-- A Yoneda section of a scheme `X` over `S` maps into `T` when the underlying
scheme morphism has image contained in `T`. -/
def mapsInto {S : Scheme.{u}} {X : Over S} (T : Set X.left)
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj X).obj U) : Prop :=
  Set.range (x : unop U ⟶ X).left ⊆ T

/-- `mapsInto T x` is the condition that the classified morphism `U ⟶ X` lands
in `T`. -/
theorem mapsInto_iff {S : Scheme.{u}} {X : Over S} (T : Set X.left)
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj X).obj U) :
    mapsInto T x ↔ Set.range (x : unop U ⟶ X).left ⊆ T :=
  sorry

/-- `mapsInto` is stable under precomposition with a morphism of schemes over
`S`. -/
theorem mapsInto_map {S : Scheme.{u}} {X : Over S} {T : Set X.left}
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) {x : (yoneda.obj X).obj U}
    (hx : mapsInto T x) :
    mapsInto T ((yoneda.obj X).map φ x) :=
  sorry

end completionAlong

/-- The functor-of-points completion of a scheme `X` over `S` along a closed
subset `T ⊆ |X|`, as the subfunctor of `yoneda.obj X` classifying morphisms
whose image of points lands in `T`. -/
def completionAlong {S : Scheme.{u}} (X : Over S) (T : Closeds X.left) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj U := { x : (yoneda.obj X).obj U // completionAlong.mapsInto (T : Set X.left) x }
  map φ := ofHom fun x ↦
    ⟨(yoneda.obj X).map φ x.1, completionAlong.mapsInto_map φ x.2⟩
  map_id := sorry
  map_comp := sorry

/-- Objects of `completionAlong X T` are Yoneda sections of `X` mapping into
`T`. -/
theorem completionAlong_obj {S : Scheme.{u}} (X : Over S) (T : Closeds X.left)
    (U : (Over S)ᵒᵖ) :
    (completionAlong X T).obj U =
      { x : (yoneda.obj X).obj U // completionAlong.mapsInto (T : Set X.left) x } :=
  sorry

namespace completionAlong

/-- The canonical morphism `completionAlong X T ⟶ yoneda.obj X` from the
completion along `T`. -/
def ι {S : Scheme.{u}} (X : Over S) (T : Closeds X.left) :
    completionAlong X T ⟶ yoneda.obj X where
  app _ := ofHom fun x ↦ x.1
  naturality := sorry

/-- Components of `ι X T` are the subtype projections of `completionAlong X T`. -/
theorem ι_app {S : Scheme.{u}} (X : Over S) (T : Closeds X.left)
    (U : (Over S)ᵒᵖ) :
    (ι X T).app U = ofHom fun x ↦ x.1 :=
  sorry

/-- A Yoneda section of `X` maps into `T` if and only if it lifts through
`ι X T`. -/
theorem exists_lift {S : Scheme.{u}} {X : Over S} (T : Closeds X.left)
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj X).obj U) :
    mapsInto (T : Set X.left) x ↔ ∃ y, (ι X T).app U y = x :=
  sorry

end completionAlong

/-- On `X = Spec(A)`, the scheme-level completion along `T` agrees with
`affineCompletionAlong`. -/
theorem completionAlong_eq_affineCompletionAlong {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    completionAlong (Over.mk structureHom) T =
      affineCompletionAlong structureHom T :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
