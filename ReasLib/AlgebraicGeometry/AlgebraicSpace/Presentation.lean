/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Presentations of algebraic spaces

This module records a presentation of an algebraic space by a scheme, an étale equivalence
relation, and a surjective étale atlas identified with the kernel pair.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A presentation of an algebraic space `F` over `S` consists of a scheme `U` over `S`, an étale
equivalence relation `R` on `U` over `S`, and a surjective étale morphism `U ⟶ F` whose kernel pair
is `R`. -/
structure Presentation {S : Scheme.{u}} (F : AlgebraicSpace S) where
  /-- The scheme over the base presenting the algebraic space. -/
  U : Over S
  /-- The étale equivalence relation on `U`. -/
  R : Scheme.PreRelation U
  /-- The atlas morphism from `U` to the functor of points of `F`. -/
  atlas : yoneda.obj U ⟶ F.functorOfPoints
  /-- `R` is an étale equivalence relation. -/
  isEtaleEquivalence : R.IsEtaleEquivalenceRelation
  /-- The atlas is representable and étale. -/
  atlas_etale : (MorphismProperty.over (@Etale)).presheaf atlas
  /-- The atlas is étale-locally surjective. -/
  atlas_locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas
  /-- The relation `R` is the kernel pair of the atlas. -/
  isKernelPair : IsKernelPair atlas (yoneda.map R.t) (yoneda.map R.s)

namespace Presentation

/-- The represented kernel pair of a representable étale atlas is an étale equivalence relation
and is the kernel pair of the atlas on functors of points. -/
theorem atlasRelation_spec {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (atlas : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf atlas) :
    let R := Scheme.PreRelation.ofHom
      (prod.lift (h_etale.rep.fst' atlas) (h_etale.rep.snd atlas))
    R.IsEtaleEquivalenceRelation ∧ IsKernelPair atlas (yoneda.map R.t) (yoneda.map R.s) := sorry

/-- Build a presentation from a representable étale locally-surjective atlas, taking the relation
to be the represented kernel pair. -/
def ofAtlas {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (atlas : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf atlas)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas) :
    Presentation F where
  U := U
  R := Scheme.PreRelation.ofHom (prod.lift (h_etale.rep.fst' atlas) (h_etale.rep.snd atlas))
  atlas := atlas
  isEtaleEquivalence := (atlasRelation_spec atlas h_etale).1
  atlas_etale := h_etale
  atlas_locallySurjective := h_surj
  isKernelPair := (atlasRelation_spec atlas h_etale).2

variable {S : Scheme.{u}} {F : AlgebraicSpace S}

/-- The scheme of `ofAtlas atlas h_etale h_surj` is the given scheme. -/
@[simp]
theorem ofAtlas_U {U : Over S} (atlas : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf atlas)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas) :
    (ofAtlas atlas h_etale h_surj).U = U := sorry

/-- The atlas of `ofAtlas atlas h_etale h_surj` is the given atlas. -/
@[simp]
theorem ofAtlas_atlas {U : Over S} (atlas : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf atlas)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas) :
    (ofAtlas atlas h_etale h_surj).atlas = atlas := sorry

/-- The relation of `ofAtlas atlas h_etale h_surj` is the represented kernel pair of the atlas. -/
theorem ofAtlas_R {U : Over S} (atlas : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf atlas)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas) :
    (ofAtlas atlas h_etale h_surj).R =
      Scheme.PreRelation.ofHom (prod.lift (h_etale.rep.fst' atlas) (h_etale.rep.snd atlas)) := sorry

/-- A presentation consists of an étale equivalence relation and a surjective étale atlas whose
kernel pair is that relation. -/
theorem spec (P : Presentation F) :
    P.R.IsEtaleEquivalenceRelation ∧
      (MorphismProperty.over (@Etale)).presheaf P.atlas ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) P.atlas ∧
          IsKernelPair P.atlas (yoneda.map P.R.t) (yoneda.map P.R.s) := sorry

/-- Every algebraic space admits a presentation. -/
theorem exists_presentation (F : AlgebraicSpace S) : Nonempty (Presentation F) := sorry

/-- The first projection of the relation of a presentation is étale. -/
theorem etale_t (P : Presentation F) : Etale P.R.t.left := sorry

/-- The second projection of the relation of a presentation is étale. -/
theorem etale_s (P : Presentation F) : Etale P.R.s.left := sorry

end Presentation

end AlgebraicGeometry.AlgebraicSpace
