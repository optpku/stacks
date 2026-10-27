/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Presheaf.Points
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Reduced induced structures on fppf sheaves

A reduced induced structure is a representable closed immersion from a sheaf
with a reduced étale atlas that induces a bijection on field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.FppfSheaf

variable {S : Scheme.{u}}

/-- A morphism of fppf sheaves over a base scheme exhibits the source as a reduced
induced structure on the target when the source is reduced, the morphism is a
closed immersion, and it is bijective on points. -/
structure IsReducedInduced {F G : Sheaf (Scheme.fppfTopology.over S) (Type (max u v))}
    (ι : F ⟶ G) : Prop where
  /-- The source admits a representable étale locally-surjective atlas from a
  reduced scheme. -/
  exists_reduced_etaleCover :
    ∃ (U : Over S)
      (p : (Scheme.fppfTopology.over S).uliftYoneda.{v}.obj U ⟶ F),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).relative
          uliftYoneda.{v} p.hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p.hom ∧
          AlgebraicGeometry.IsReduced U.left
  /-- The morphism is a closed immersion of fppf sheaves. -/
  isClosedImmersion :
    (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).relative
      uliftYoneda.{v} ι.hom
  /-- The morphism is bijective on points. -/
  bijectiveOnPoints : Function.Bijective (SpacePresheaf.Points.map ι.hom)

/-- Construct `IsReducedInduced` from a reduced étale atlas, a closed immersion,
and bijectivity on points. -/
def IsReducedInduced.of {F G : Sheaf (Scheme.fppfTopology.over S) (Type (max u v))}
    (ι : F ⟶ G)
    (exists_reduced_etaleCover :
      ∃ (U : Over S)
        (p : (Scheme.fppfTopology.over S).uliftYoneda.{v}.obj U ⟶ F),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).relative
            uliftYoneda.{v} p.hom ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p.hom ∧
            AlgebraicGeometry.IsReduced U.left)
    (isClosedImmersion :
      (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).relative
        uliftYoneda.{v} ι.hom)
    (bijectiveOnPoints : Function.Bijective (SpacePresheaf.Points.map ι.hom)) :
    IsReducedInduced ι where
  exists_reduced_etaleCover := exists_reduced_etaleCover
  isClosedImmersion := isClosedImmersion
  bijectiveOnPoints := bijectiveOnPoints

/-- A morphism exhibits a reduced induced structure exactly when its source
has a reduced étale atlas and it is a closed immersion bijective on points. -/
theorem IsReducedInduced.iff {F G : Sheaf (Scheme.fppfTopology.over S) (Type (max u v))}
    (ι : F ⟶ G) :
    IsReducedInduced ι ↔
      (∃ (U : Over S)
          (p : (Scheme.fppfTopology.over S).uliftYoneda.{v}.obj U ⟶ F),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).relative
              uliftYoneda.{v} p.hom ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p.hom ∧
              AlgebraicGeometry.IsReduced U.left) ∧
        (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).relative
            uliftYoneda.{v} ι.hom ∧
          Function.Bijective (SpacePresheaf.Points.map ι.hom) :=
  sorry

end AlgebraicGeometry.FppfSheaf
