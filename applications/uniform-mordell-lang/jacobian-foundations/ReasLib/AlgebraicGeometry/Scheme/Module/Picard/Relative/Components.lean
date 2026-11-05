module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Curve.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties
public import ReasLib.CategoryTheory.RepresentablePresheaf

/-!
# Degree components of the relative Picard scheme

This file defines the relative-degree locus in the Picard functor, its represented
components, and their basic geometric properties for smooth projective curves.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.RelativePicard

/-- For a proper curve, fiber Euler characteristics commute with field extension,
so the base-change-stable definition is exactly ordinary relative degree. -/
theorem mem_degreePresheaf_of_properCurve {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] [IsProper X.hom] (d : ℤ)
    (T : (SchemeOverField k)ᵒᵖ) (x : (presheaf X).obj T) :
    x ∈ (degreePresheaf X d).obj T ↔ relativeDegree X T x = fun _ ↦ d := by
  sorry

/-- Degree-`d` Picard classes of a proper curve over a field. -/
noncomputable def degreeClasses {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [IsProper X.hom] (d : ℤ) : Set X.left.PicardGroup :=
  {x | Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le (Scheme.PicardGroup.repr x) = d}

/-- Membership in `degreeClasses X d` means that the chosen invertible representative has
curve degree `d`. -/
theorem mem_degreeClasses {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [IsProper X.hom] (d : ℤ) (x : X.left.PicardGroup) :
    x ∈ degreeClasses X d ↔ Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le (Scheme.PicardGroup.repr x) = d := sorry

/-- The degree-`d` relative Picard subfunctor of a smooth projective curve over a separably
closed field is representable. -/
instance degreeSubfunctor_isRepresentable
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℤ) :
    (degreeSubfunctor X d).toFunctor.IsRepresentable := sorry

/-- The chosen scheme representing the degree-`d` part of the relative Picard functor. -/
noncomputable def component {S : Scheme.{u}} (X : Over S) (d : ℤ)
    [(degreeSubfunctor X d).toFunctor.IsRepresentable] : Over S :=
  (degreeSubfunctor X d).toFunctor.reprX

/-- The canonical representation of the degree-`d` relative Picard component. -/
noncomputable def componentRepresentation {S : Scheme.{u}} (X : Over S) (d : ℤ)
    [(degreeSubfunctor X d).toFunctor.IsRepresentable] :
    (degreeSubfunctor X d).toFunctor.RepresentableBy (component X d) :=
  (degreeSubfunctor X d).toFunctor.representableBy

/-- The canonical morphism from a degree component to the relative Picard scheme. -/
noncomputable def componentInclusion {S : Scheme.{u}} (X : Over S) (d : ℤ)
    [(degreeSubfunctor X d).toFunctor.IsRepresentable] [(functor X).obj.IsRepresentable] :
    component X d ⟶ scheme X :=
  (componentRepresentation X d).map (schemeRepresentation X) (degreeSubfunctor X d).ι

/-- Under the representing equivalence, `componentInclusion` is the inclusion of the
degree subfunctor into the relative Picard functor. -/
theorem componentInclusion_homEquiv {S : Scheme.{u}} (X : Over S) (d : ℤ)
    [(degreeSubfunctor X d).toFunctor.IsRepresentable] [(functor X).obj.IsRepresentable] :
    (schemeRepresentation X).homEquiv (componentInclusion X d) =
      (degreeSubfunctor X d).ι.app (op (component X d))
        ((componentRepresentation X d).homEquiv (𝟙 (component X d))) := sorry

/-- A degree-`d` Picard class over `k`, viewed as a section of the Picard functor over
`Spec k`. -/
noncomputable def degreeClassSection
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (d : ℤ) (x : degreeClasses X d) :
    (functor X).obj.obj (op (𝟙_ (SchemeOverField k))) :=
  ((Scheme.fppfTopology.over (Spec (CommRingCat.of k))).toSheafify
    (presheaf X)).app _
      (Scheme.Hom.picardPullback (λ_ X).hom.left x.1)

/-- A degree-`d` class maps into the degree-`d` Picard subfunctor. -/
theorem degreeClassSection_mem_degreeSubfunctor
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (d : ℤ) (x : degreeClasses X d) :
    degreeClassSection X d x ∈
      (degreeSubfunctor X d).obj (op (𝟙_ (SchemeOverField k))) := sorry

/-- A degree-`d` Picard class over `k`, mapped canonically to the represented degree
component. -/
noncomputable def degreeClassToComponentPoint
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℤ) :
    degreeClasses X d → ((𝟙_ (SchemeOverField k)) ⟶ component X d) :=
  fun x ↦ (componentRepresentation X d).homEquiv.symm
    ⟨degreeClassSection X d x, degreeClassSection_mem_degreeSubfunctor X d x⟩

/-- Every degree component of the Picard scheme is open. -/
instance componentInclusion_isOpenImmersion
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℤ) :
    IsOpenImmersion (componentInclusion X d).left := sorry

/-- Every degree component of the Picard scheme is closed. -/
instance componentInclusion_isClosedImmersion
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℤ) :
    IsClosedImmersion (componentInclusion X d).left := sorry

/-- The images of distinct degree components in the Picard scheme are disjoint. -/
theorem componentInclusion_pairwiseDisjoint
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] :
    Pairwise fun d e : ℤ ↦ Disjoint
      (Set.range (componentInclusion X d).left.base)
      (Set.range (componentInclusion X e).left.base) := sorry

/-- The integer-degree components cover the Picard scheme. -/
theorem iUnion_range_componentInclusion
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] :
    (⋃ d : ℤ, Set.range (componentInclusion X d).left.base) = Set.univ := sorry

/-- Each degree component is smooth of relative dimension equal to the genus. -/
instance component_smoothOfRelativeDimension
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℤ) :
    SmoothOfRelativeDimension (Curve.genus X) (component X d).hom := sorry

/-- Each degree component is a proper variety over the base field. -/
instance component_properVariety
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℤ) :
    ProperVariety (component X d) := sorry

/-- The `k`-points of the degree-`d` component correspond bijectively to invertible
`𝒪_X`-modules of degree `d`, through their Picard classes. -/
theorem degreeClassToComponentPoint_bijective
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℤ) :
    Function.Bijective (degreeClassToComponentPoint X d) := sorry

end AlgebraicGeometry.RelativePicard
