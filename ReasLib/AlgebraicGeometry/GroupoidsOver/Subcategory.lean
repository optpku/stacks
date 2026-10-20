module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology

/-!
# Full subcategories of associated sites

A full subcategory of the total category of a groupoid fibration may be
stable under morphisms lying over a given class of scheme maps, may contain
a smooth surjective atlas object, and inherits the associated `τ`-topology
along the inclusion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- There exists an object of `Q` whose associated 1-morphism
`(Sch / U)_fppf ⟶ X` is smooth and surjective. -/
def ExistsSmoothSurjectiveObject {X : GroupoidsOver S}
    (Q : ObjectProperty X.total) : Prop :=
  ∃ x : X.total,
    Q x ∧
      Groupoids.Hom.Smooth
          (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) ∧
        Groupoids.Hom.Surjective
          (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x)))

/-- Unfolding of `ExistsSmoothSurjectiveObject` as an object of `Q` whose
Yoneda representative is a smooth surjective 1-morphism. -/
theorem ExistsSmoothSurjectiveObject.exists_iff {X : GroupoidsOver S}
    (Q : ObjectProperty X.total) :
    ExistsSmoothSurjectiveObject Q ↔
      ∃ x : X.total,
        Q x ∧
          Groupoids.Hom.Smooth
              (YonedaSlice.representative
                (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) ∧
            Groupoids.Hom.Surjective
              (YonedaSlice.representative
                (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) :=
  sorry

/-- The Grothendieck topology on a full subcategory of `X` whose covering
families are the families of morphisms in the subcategory that cover in the
associated `τ`-site of `X`. -/
abbrev subcategoryTopology (X : GroupoidsOver S) (τ : StandardTopology)
    (Q : ObjectProperty X.total) : GrothendieckTopology Q.FullSubcategory :=
  Q.ι.restrictedTopology (X.associatedTopology τ)

/-- `subcategoryTopology X τ Q` is the restricted topology of the associated
`τ`-site of `X` along the inclusion of `Q`. -/
theorem subcategoryTopology_eq (X : GroupoidsOver S) (τ : StandardTopology)
    (Q : ObjectProperty X.total) :
    subcategoryTopology X τ Q =
      Q.ι.restrictedTopology (X.associatedTopology τ) :=
  sorry

/-- A represented family in a full subcategory is a declared covering for the
induced `τ`-site if and only if the image family covers in the associated
`τ`-site of `X`. This is membership in the comap precoverage generating
`subcategoryTopology`, not sieve membership in the saturated restricted
topology. -/
theorem ofArrows_mem_subcategoryTopology_iff (X : GroupoidsOver S)
    (τ : StandardTopology) (Q : ObjectProperty X.total)
    {x : Q.FullSubcategory} {ι : Type w} (Y : ι → Q.FullSubcategory)
    (f : ∀ i, Y i ⟶ x) :
    Presieve.ofArrows Y f ∈
        ((X.associatedTopology τ).toPrecoverage.comap Q.ι) x ↔
      Sieve.generate
          (Presieve.ofArrows (fun i ↦ Q.ι.obj (Y i)) (fun i ↦ Q.ι.map (f i))) ∈
        X.associatedTopology τ (Q.ι.obj x) :=
  sorry

/-- The inclusion of a full subcategory stable under morphisms lying over
smooth scheme maps is continuous for the induced étale topologies. -/
instance inclusion_isContinuous_etale {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))] :
    Q.ι.IsContinuous (subcategoryTopology X StandardTopology.etale Q)
      X.etaleTopology :=
  sorry

/-- The inclusion of a full subcategory stable under morphisms lying over
smooth scheme maps is cocontinuous for the induced étale topologies. -/
instance inclusion_isCocontinuous_etale {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))] :
    Q.ι.IsCocontinuous (subcategoryTopology X StandardTopology.etale Q)
      X.etaleTopology :=
  sorry

/-- The inclusion of a full subcategory stable under morphisms lying over
flat and locally finitely presented scheme maps is continuous for the induced
fppf topologies. -/
instance inclusion_isContinuous_fppf {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))] :
    Q.ι.IsContinuous (subcategoryTopology X StandardTopology.fppf Q)
      X.fppfTopology :=
  sorry

/-- The inclusion of a full subcategory stable under morphisms lying over
flat and locally finitely presented scheme maps is cocontinuous for the induced
fppf topologies. -/
instance inclusion_isCocontinuous_fppf {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))] :
    Q.ι.IsCocontinuous (subcategoryTopology X StandardTopology.fppf Q)
      X.fppfTopology :=
  sorry

end AlgebraicGeometry.GroupoidsOver
