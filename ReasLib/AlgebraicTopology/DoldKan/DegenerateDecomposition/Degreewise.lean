/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Projection
public import ReasLib.AlgebraicTopology.DoldKan.Normalized
public import ReasLib.Algebra.Homology.HomologicalComplex.Biproduct
public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Functor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise normalized--degenerate decomposition

This leaf owns the source-facing decomposition using the explicit degreewise degenerate complex.
The canonical `QInfty` image presentation and its comparison are provided by sibling leaves.

@stack 019A
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace degenerateComplex.decomposition

/-- The degreewise normalized--degenerate decomposition map. -/
@[stacks 019A "normalized-degenerate decomposition map"]
def hom (U : SimplicialObject A) : K[U] ⟶ N[U] ⊞ D[U] :=
  biprod.lift (PInftyToNormalizedMooreComplex U) (degenerateComplex.π U)

/-- The degreewise normalized--degenerate reconstruction map. -/
@[stacks 019A "normalized-degenerate reconstruction map"]
def inv (U : SimplicialObject A) : N[U] ⊞ D[U] ⟶ K[U] :=
  biprod.desc (inclusionOfMooreComplexMap U) (degenerateComplex.ι U)

/-- The forward and backward maps in the normalized-plus-degenerate decomposition compose to the
identity on the alternating-face complex. -/
@[reassoc, stacks 019A "normalized-degenerate decomposition inverse law"]
theorem hom_comp_inv (U : SimplicialObject A) :
    hom U ≫ inv U = 𝟙 K[U] := sorry

/-- The backward and forward maps in the normalized-plus-degenerate decomposition compose to the
identity on the biproduct. -/
@[reassoc, stacks 019A "normalized-degenerate decomposition inverse law"]
theorem inv_comp_hom (U : SimplicialObject A) :
    inv U ≫ hom U = 𝟙 (N[U] ⊞ D[U]) := sorry

end degenerateComplex.decomposition

namespace degenerateComplex

/-- The alternating-face complex of a simplicial object splits as its normalized Moore complex and
its degenerate subcomplex. -/
@[stacks 019A "Dold-Kan normalized-degenerate decomposition"]
def decomposition (U : SimplicialObject A) : K[U] ≅ N[U] ⊞ D[U] where
  hom := decomposition.hom U
  inv := decomposition.inv U
  hom_inv_id := decomposition.hom_comp_inv U
  inv_hom_id := decomposition.inv_comp_hom U

namespace decomposition

/-- The forward map of the Dold--Kan decomposition is the pair of normalized and degenerate
projections. -/
@[stacks 019A "normalized-degenerate decomposition forward map"]
theorem hom_eq (U : SimplicialObject A) :
    (decomposition U).hom =
      biprod.lift (PInftyToNormalizedMooreComplex U) (degenerateComplex.π U) := sorry

/-- The named degreewise decomposition map is the explicit biproduct lift. -/
@[simp, stacks 019A "normalized-degenerate decomposition map formula"]
theorem hom_def (U : SimplicialObject A) :
    decomposition.hom U =
      biprod.lift (PInftyToNormalizedMooreComplex U) (degenerateComplex.π U) := sorry

/-- The inverse Dold--Kan decomposition map is induced by the normalized and degenerate
inclusions. -/
@[stacks 019A "normalized-degenerate decomposition inverse map"]
theorem inv_eq (U : SimplicialObject A) :
    (decomposition U).inv =
      biprod.desc (inclusionOfMooreComplexMap U) (degenerateComplex.ι U) := sorry

/-- The named degreewise reconstruction map is the explicit biproduct descent. -/
@[simp, stacks 019A "normalized-degenerate reconstruction map formula"]
theorem inv_def (U : SimplicialObject A) :
    decomposition.inv U =
      biprod.desc (inclusionOfMooreComplexMap U) (degenerateComplex.ι U) := sorry

/-- The normalized inclusion becomes the left biproduct inclusion after the Dold--Kan
decomposition. -/
@[reassoc, stacks 019A "normalized inclusion coordinate of the decomposition"]
theorem inclusion_comp_hom (U : SimplicialObject A) :
    inclusionOfMooreComplexMap U ≫ (decomposition U).hom = biprod.inl := sorry

/-- The normalized projection is the left biproduct projection after the Dold--Kan decomposition.
-/
@[reassoc, stacks 019A "normalized projection coordinate of the decomposition"]
theorem hom_comp_fst (U : SimplicialObject A) :
    (decomposition U).hom ≫ biprod.fst = PInftyToNormalizedMooreComplex U := sorry

/-- The degenerate projection is the right biproduct projection after the Dold--Kan decomposition.
-/
@[reassoc, stacks 019A "degenerate projection coordinate of the decomposition"]
theorem hom_comp_snd (U : SimplicialObject A) :
    (decomposition U).hom ≫ biprod.snd = degenerateComplex.π U := sorry

namespace degenerate.ι

/-- The degenerate inclusion becomes the right biproduct inclusion after the Dold--Kan
decomposition. -/
@[reassoc, stacks 019A "degenerate inclusion coordinate of the decomposition"]
theorem comp_hom (U : SimplicialObject A) :
    degenerateComplex.ι U ≫ (decomposition U).hom = biprod.inr := sorry

end degenerate.ι

/-- The inverse Dold--Kan decomposition sends the left biproduct inclusion to the normalized
inclusion. -/
@[reassoc, stacks 019A "normalized inclusion coordinate of the inverse decomposition"]
theorem inl_comp_inv (U : SimplicialObject A) :
    biprod.inl ≫ (decomposition U).inv = inclusionOfMooreComplexMap U := sorry

/-- The inverse Dold--Kan decomposition sends the right biproduct inclusion to the degenerate
inclusion. -/
@[reassoc, stacks 019A "degenerate inclusion coordinate of the inverse decomposition"]
theorem inr_comp_inv (U : SimplicialObject A) :
    biprod.inr ≫ (decomposition U).inv = degenerateComplex.ι U := sorry

namespace degenerate.ι

/-- The degreewise degenerate inclusion has zero component in the normalized Moore summand. -/
@[reassoc, stacks 019A "degenerate inclusion annihilates the normalized projection"]
theorem comp_projection (U : SimplicialObject A) :
    degenerateComplex.ι U ≫ PInftyToNormalizedMooreComplex U = 0 := sorry

end degenerate.ι

namespace inclusion

/-- The normalized inclusion has zero component in the degreewise degenerate summand. -/
@[reassoc, stacks 019A "normalized inclusion annihilates the degenerate projection"]
theorem comp_degenerateProjection (U : SimplicialObject A) :
    inclusionOfMooreComplexMap U ≫ degenerateComplex.π U = 0 := sorry

end inclusion

/-- The normalized and degreewise degenerate projectors sum to the identity on the alternating-face
complex. -/
@[stacks 019A "normalized-degenerate projector sum"]
theorem projector_sum (U : SimplicialObject A) :
    (PInftyToNormalizedMooreComplex U ≫ inclusionOfMooreComplexMap U : K[U] ⟶ K[U]) +
        degenerateComplex.π U ≫ degenerateComplex.ι U = 𝟙 K[U] := sorry

/-- The natural projection from alternating-face complexes to their normalized and degenerate
summands. -/
@[stacks 019A "normalized-degenerate decomposition projection"]
def toSummand :
    alternatingFaceMapComplex A ⟶
      (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A) :=
  biprod.lift (projectionToMooreComplex A) degenerateComplex.π.natTrans

/-- The natural comparison from the normalized and degenerate summands to alternating-face
complexes. -/
@[stacks 019A "normalized-degenerate decomposition comparison"]
def fromSummand :
    (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A) ⟶
      alternatingFaceMapComplex A :=
  biprod.desc (inclusionOfMooreComplex A) degenerateComplex.ι.natTrans

/-- The decomposition projection followed by its comparison is the identity on alternating-face
complexes. -/
@[stacks 019A "normalized-degenerate decomposition inverse law"]
theorem to_comp_from :
    toSummand (A := A) ≫ fromSummand (A := A) =
      𝟙 (alternatingFaceMapComplex A) := sorry

/-- The comparison followed by the decomposition projection is the identity on the biproduct
functor. -/
@[stacks 019A "normalized-degenerate decomposition inverse law"]
theorem from_comp_to :
    fromSummand (A := A) ≫ toSummand (A := A) =
      𝟙 ((normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A)) := sorry

/-- The Dold--Kan decomposition as a natural isomorphism from alternating-face complexes to the
canonical biproduct of normalized and degenerate complexes. -/
@[stacks 019A "normalized-degenerate decomposition natural isomorphism"]
def natIso :
    alternatingFaceMapComplex A ≅
      (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A) where
  hom := toSummand
  inv := fromSummand
  hom_inv_id := to_comp_from
  inv_hom_id := from_comp_to

/-- The evaluation of the functorial biproduct target is identified with the objectwise target. -/
@[stacks 019A "evaluation bridge for the source-facing Dold-Kan decomposition target"]
noncomputable def evalIso (U : SimplicialObject A) :
    ((normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A)).obj U ≅
      N[U] ⊞ D[U] :=
  CategoryTheory.Limits.evalBiprodIso (normalizedMooreComplex A)
    (degenerateComplex.functor (C := A)) U

/-- After the evaluation bridge, the functorial source-facing decomposition is the objectwise one. -/
@[stacks 019A "component of the source-facing Dold-Kan decomposition"]
theorem natIso.app (U : SimplicialObject A) :
    (natIso (A := A)).app U ≪≫ evalIso U = decomposition U := sorry

/-- The forward evaluated degreewise decomposition is the objectwise forward decomposition map. -/
@[stacks 019A "forward degreewise decomposition component"]
theorem natIso.hom_app (U : SimplicialObject A) :
    (natIso (A := A)).hom.app U ≫ (evalIso U).hom = (decomposition U).hom := sorry

/-- The inverse of the evaluated degreewise decomposition is the inverse evaluation bridge followed
by the inverse functor-category component. -/
@[stacks 019A "inverse degreewise decomposition component"]
theorem natIso.inv_app (U : SimplicialObject A) :
    (evalIso U).inv ≫ (natIso (A := A)).inv.app U = (decomposition U).inv := sorry

/-- The normalized coordinate of the functorial decomposition projection is the canonical Moore
projection. -/
@[reassoc, stacks 019A "normalized coordinate of the functorial decomposition"]
theorem toSummand.app_fst (U : SimplicialObject A) :
    (toSummand (A := A)).app U ≫
      ((biprod.fst : (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A) ⟶
        normalizedMooreComplex A).app U) = PInftyToNormalizedMooreComplex U := sorry

/-- The degenerate coordinate of the functorial decomposition projection is the canonical
degenerate projection. -/
@[reassoc, stacks 019A "degenerate coordinate of the functorial decomposition"]
theorem toSummand.app_snd (U : SimplicialObject A) :
    (toSummand (A := A)).app U ≫
      ((biprod.snd : (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A) ⟶
        degenerateComplex.functor (C := A)).app U) = degenerateComplex.π U := sorry

/-- On the normalized coordinate, the comparison to alternating-face complexes is the canonical
Moore inclusion. -/
@[reassoc, stacks 019A "normalized coordinate of the functorial comparison"]
theorem fromSummand.inl_app (U : SimplicialObject A) :
    ((biprod.inl : normalizedMooreComplex A ⟶
        (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A)).app U) ≫
      (fromSummand (A := A)).app U = inclusionOfMooreComplexMap U := sorry

/-- On the degenerate coordinate, the comparison to alternating-face complexes is the canonical
degenerate inclusion. -/
@[reassoc, stacks 019A "degenerate coordinate of the functorial comparison"]
theorem fromSummand.inr_app (U : SimplicialObject A) :
    ((biprod.inr : degenerateComplex.functor (C := A) ⟶
        (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A)).app U) ≫
      (fromSummand (A := A)).app U = degenerateComplex.ι U := sorry

/-- The forward map of the functorial Dold--Kan decomposition is its canonical projection. -/
@[simp, stacks 019A "functorial Dold-Kan decomposition forward map"]
theorem natIso.hom_eq :
    (natIso (A := A)).hom = toSummand (A := A) := sorry

/-- The inverse map of the functorial Dold--Kan decomposition is its canonical comparison. -/
@[simp, stacks 019A "functorial Dold-Kan decomposition inverse map"]
theorem natIso.inv_eq :
    (natIso (A := A)).inv = fromSummand (A := A) := sorry

end decomposition

end degenerateComplex

end AlgebraicTopology.DoldKan
