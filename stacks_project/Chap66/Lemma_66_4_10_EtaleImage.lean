module

public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import stacks_project.Chap65.Definition_65_9_3_Presentation
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair
public import stacks_project.Chap66.Lemma_66_4_4_Surjective
public import stacks_project.Chap66.Lemma_66_4_9_Lift

/-!
# Étale images as open subspaces

An étale morphism from a scheme to an algebraic space factors through the open subspace
cut out by its image of points as a surjective étale morphism. The original kernel pair
remains a kernel pair of that lift, and the same relation presents the open image as `U/R`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Points

/-- The image of points of an étale morphism from a scheme is open in the canonical topology. -/
theorem isOpen_range_map_of_etale {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f) :
    IsOpen (Set.range (Points.map f)) :=
  sorry

end Points

namespace OpenSubspace

/-- There is an open subspace whose underlying points are the image of an étale morphism from a
scheme. -/
theorem exists_of_etale {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f) :
    ∃ X' : OpenSubspace X, X'.pointsSet = Set.range (Points.map f) :=
  sorry

/-- An étale morphism from a scheme factors through the open subspace on its image of points as a
surjective étale morphism. -/
theorem exists_surjective_etale_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f)) :
    ∃ f' : ofOver U ⟶ X'.X, f' ≫ X'.ι = f ∧
      (MorphismProperty.over (@Etale)).presheaf f' ∧
        (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f' :=
  sorry

/-- Factorization of an étale morphism from a scheme through the open subspace on its image of
points is unique. -/
theorem existsUnique_etale_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f)) :
    ∃! f' : ofOver U ⟶ X'.X, f' ≫ X'.ι = f :=
  sorry

/-- Any factorization of an étale morphism from a scheme through the open subspace on its image of
points is étale. -/
theorem etale_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    (MorphismProperty.over (@Etale)).presheaf f' :=
  sorry

/-- Any factorization of an étale morphism from a scheme through the open subspace on its image of
points is surjective in the sense of Spaces, Definition 65.5.1. -/
theorem surjective_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f' :=
  sorry

/-- Any factorization of an étale morphism from a scheme through the open subspace on its image of
points is surjective on points. -/
theorem surjective_points_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    Function.Surjective (Points.map f') :=
  sorry

/-- Any factorization of an étale morphism from a scheme through the open subspace on its image of
points is étale-locally surjective. -/
theorem locallySurjective_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f' :=
  sorry

/-- The represented kernel pair of an étale morphism from a scheme remains a kernel pair of any
factorization through the open subspace on its image of points. -/
theorem isKernelPair_etale_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : yoneda.obj U ⟶ X'.X.functorOfPoints} (hfac : f' ≫ X'.ι = f) :
    IsKernelPair f' (yoneda.map (kernelPair f hf.rep).t)
      (yoneda.map (kernelPair f hf.rep).s) :=
  sorry

/-- The presentation of the open étale image by the original scheme atlas and the represented
kernel pair `R = U ×_X U`. -/
noncomputable def presentation {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    Presentation X'.X where
  U := U
  R := kernelPair f hf.rep
  atlas := f'
  isEtaleEquivalence := sorry
  atlas_etale := sorry
  atlas_locallySurjective := sorry
  isKernelPair := sorry

/-- The presentation of the open étale image is `X' = U/R` for the original scheme `U` and
the represented kernel pair `R = U ×_X U`. -/
theorem presentation_spec {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    (presentation hf X' hX' hfac).U = U ∧
      (presentation hf X' hX' hfac).R = kernelPair f hf.rep ∧
        (presentation hf X' hX' hfac).atlas = f' :=
  sorry

end OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
