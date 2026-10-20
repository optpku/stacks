module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.RelativeDimensionLocus
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.ComponentRestriction

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom

/-- On a dimension-`r` locus, the degree-`p` flat coefficient is ordinary flat pullback
when `p = -r`, and zero otherwise. -/
def flatPullbackComponentDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Flat f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left] (p : ℤ) (r : ℕ) :
    @BivariantClass S inferInstance δ inferInstance
      (ComponentRestriction.over X (flatLciDimensionLocus f.left r))
      (ComponentRestriction.over Y ⊤)
      (ComponentRestriction.locallyOfFiniteTypeOver X _)
      (ComponentRestriction.locallyOfFiniteTypeOver Y _)
      (ComponentRestriction.hom f (flatLciDimensionLocus f.left r) ⊤ (by simp)) p :=
  if h : -(r : ℤ) = p then
    h ▸ @flatPullback S inferInstance δ inferInstance
      (ComponentRestriction.over X (flatLciDimensionLocus f.left r))
      (ComponentRestriction.over Y ⊤)
      (ComponentRestriction.locallyOfFiniteTypeOver X _)
      (ComponentRestriction.locallyOfFiniteTypeOver Y _)
      (ComponentRestriction.hom f (flatLciDimensionLocus f.left r) ⊤ (by simp)) r
      (inferInstance : Flat (f.left.resLE ⊤ (flatLciDimensionLocus f.left r) (by simp)))
      (relativeDimension_flatLciDimensionLocus f.left r)
  else pointwiseZero δ
    (ComponentRestriction.hom f (flatLciDimensionLocus f.left r) ⊤ (by simp)) p

/-- The matching-degree component is the usual flat-pullback class of that dimension
locus. -/
theorem flatPullbackComponentDegree_neg
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Flat f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left] (r : ℕ) :
    flatPullbackComponentDegree δ f (-(r : ℤ)) r =
      @flatPullback S inferInstance δ inferInstance
        (ComponentRestriction.over X (flatLciDimensionLocus f.left r))
        (ComponentRestriction.over Y ⊤)
        (ComponentRestriction.locallyOfFiniteTypeOver X _)
        (ComponentRestriction.locallyOfFiniteTypeOver Y _)
        (ComponentRestriction.hom f (flatLciDimensionLocus f.left r) ⊤ (by simp)) r
        (inferInstance : Flat (f.left.resLE ⊤ (flatLciDimensionLocus f.left r) (by simp)))
        (relativeDimension_flatLciDimensionLocus f.left r) := sorry

/-- The degree-`p` flat-pullback coefficient assembled from the disjoint clopen
fiber-dimension loci. -/
def flatPullbackDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Flat f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left] (p : ℤ) :
    BivariantClass δ f p :=
  ComponentRestriction.assemble δ f p (flatLciDimensionLocus f.left)
    (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
    (flatLciDimensionLocus_iSup f.left) (by simp)
    (flatLciDimensionLocus_pairwiseDisjoint f.left)
    (by intro a b h; exact (h (Subsingleton.elim a b)).elim)
    (fun r ↦ flatLciDimensionLocus_isClopen f.left r) (fun _ ↦ isClopen_univ)
    (fun _ ↦ by simp) (flatPullbackComponentDegree δ f p)

/-- Restricting the assembled flat coefficient recovers its dimension-locus component. -/
theorem flatPullbackDegree_component
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Flat f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left] (p : ℤ) (r : ℕ) :
    ComponentRestriction.restrict δ f p (flatLciDimensionLocus f.left r) ⊤ (by simp)
        (flatPullbackDegree δ f p) = flatPullbackComponentDegree δ f p r := sorry

end AlgebraicGeometry.BivariantClass
