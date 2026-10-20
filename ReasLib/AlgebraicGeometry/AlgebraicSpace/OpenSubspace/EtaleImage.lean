/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Factorization

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
points is representably surjective. -/
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
  isEtaleEquivalence := (Presentation.atlasRelation_spec f hf).1
  atlas_etale := etale_lift hf X' hX' hfac
  atlas_locallySurjective := locallySurjective_lift hf X' hX' hfac
  isKernelPair := isKernelPair_etale_lift hf X' hX' hfac

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
