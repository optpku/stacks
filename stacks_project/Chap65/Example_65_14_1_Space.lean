/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import stacks_project.Chap65.Example_65_14_1_Relation

/-!
# The affine-line involution algebraic space

This module records the fppf sheaf quotient `X = U / R` of the affine line by the étale
equivalence relation of `Example_65_14_1_Relation`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The fppf sheaf `X = U / R`, obtained by sheafifying the universe-raised quotient presheaf. -/
def sheafOfPoints (k : Type u) [Field k] :
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)) :=
  (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k))

/-- `sheafOfPoints k` is the fppf quotient sheaf of the affine-line involution pre-relation. -/
theorem sheafOfPoints_eq (k : Type u) [Field k] :
    sheafOfPoints k = (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k)) := sorry

/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical quotient map. -/
def atlas (k : Type u) [Field k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶ sheafOfPoints k :=
  (preRelation k).quotientMap (Scheme.fppfTopology.over (base k))

/-- The atlas is the canonical fppf quotient map of the pre-relation. -/
theorem atlas_eq (k : Type u) [Field k] :
    atlas k = (preRelation k).quotientMap (Scheme.fppfTopology.over (base k)) := sorry

/-- The fppf quotient sheaf `X = U / R` is an algebraic space over `Spec k`: it has a
representable étale locally-surjective atlas from `U` and a representable diagonal. -/
theorem sheafOfPoints_spec (k : Type u) [Field k] [NeZero (2 : k)] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom ∧
        uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) := sorry

/-- The diagonal of `X = U / R` is quasi-compact relative to `uliftYoneda`, so `X` is
quasi-separated. -/
theorem quasiCompact_diag_sheafOfPoints (k : Type u) [Field k] [NeZero (2 : k)] :
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k).obj) := sorry

/-- The diagonal of `X = U / R` is not an immersion relative to `uliftYoneda`, so `X` is not
locally separated. -/
theorem not_isImmersion_diag_sheafOfPoints (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ (MorphismProperty.over (@IsImmersion)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
