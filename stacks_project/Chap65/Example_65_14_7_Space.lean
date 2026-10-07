module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import stacks_project.Chap65.Example_65_14_7_ArtinSchreier
public import stacks_project.Chap65.Lemma_65_14_6_Equivariant

/-!
# The algebraic space `Spec algebraicQ / Gal(algebraicQ / ℚ)`

This module records the canonical Galois action of `gal` on `Spec algebraicQ` over `Spec ℚ`,
the residue-field-free hypothesis `(*)`, and the fppf quotient sheaf `X = U / G`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- The base scheme `S = Spec ℚ`. -/
abbrev base : Scheme.{0} := Spec (CommRingCat.of ℚ)

/-- The base scheme is the spectrum of `ℚ`. -/
theorem base_eq : base = Spec (CommRingCat.of ℚ) := sorry

/-- The cover `U = Spec algebraicQ` as a scheme over `Spec ℚ`. -/
def cover : Over base :=
  Over.mk (FieldExtension.specMap ℚ algebraicQ)

/-- The underlying scheme of the cover is `Spec algebraicQ`. -/
theorem cover_left : cover.left = Spec (CommRingCat.of algebraicQ) := sorry

/-- The structure morphism of the cover is the canonical map `Spec algebraicQ ⟶ Spec ℚ`. -/
theorem cover_hom : cover.hom = FieldExtension.specMap ℚ algebraicQ := sorry

/-- The Galois automorphism of `Spec algebraicQ` induced by `σ` lies over `Spec ℚ`. -/
theorem action_w (σ : gal) : (galSpecAut σ).hom ≫ cover.hom = cover.hom := sorry

/-- The obvious action of `Gal(algebraicQ / ℚ)` on `U = Spec algebraicQ` over `S`.
The underlying scheme map uses the inverse convention of `galSpecAut`. -/
def action : gal →* Aut cover where
  toFun σ := Over.isoMk (galSpecAut σ) (action_w σ)
  map_one' := sorry
  map_mul' := sorry

/-- The underlying scheme morphism of `action σ` is `galSpecMap σ⁻¹`. -/
theorem action_hom (σ : gal) : (action σ).hom.left = galSpecMap σ⁻¹ := sorry

/-- The identity Galois element acts by the identity automorphism of the cover. -/
theorem action_one : action 1 = 1 := sorry

/-- Property `(*)` of Lemma 65.14.3: the Galois action is residue-field free. -/
instance instIsResidueFieldFree_action : IsResidueFieldFree action := sorry

/-- The fppf sheaf `X = U / G`, obtained by sheafifying the universe-raised quotient presheaf. -/
def sheafOfPoints : Sheaf (Scheme.fppfTopology.over base) (Type 1) :=
  (ofAut action).quotientSheaf (Scheme.fppfTopology.over base)

/-- `sheafOfPoints` is the fppf quotient sheaf of the Galois pre-relation `ofAut action`. -/
theorem sheafOfPoints_eq :
    sheafOfPoints = (ofAut action).quotientSheaf (Scheme.fppfTopology.over base) := sorry

/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical quotient map. -/
def atlas :
    (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover ⟶ sheafOfPoints :=
  (ofAut action).quotientMap (Scheme.fppfTopology.over base)

/-- The atlas is the canonical fppf quotient map of `ofAut action`. -/
theorem atlas_eq : atlas = (ofAut action).quotientMap (Scheme.fppfTopology.over base) := sorry

/-- The fppf quotient sheaf `X = U / G` is an algebraic space over `Spec ℚ`: it has a
representable étale locally-surjective atlas from `U` and a representable diagonal. -/
theorem sheafOfPoints_spec :
    uliftYoneda.{1}.relativelyRepresentable (diag sheafOfPoints.obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{1} atlas.hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) atlas.hom := sorry

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
