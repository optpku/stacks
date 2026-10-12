/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Signed
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting.LowerFace
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Map
public import ReasLib.Algebra.Homology.HomologicalComplex.Biproduct
public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Functor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-signed normalized--degenerate decomposition

This leaf owns the Stacks convention for the normalized Moore summand: the intersection of the
lower-face kernels with differential `(-1)^n d_n`.  The alternating-face complex is the ambient
complex, and the degreewise degenerate complex is its complementary summand.  The older Mathlib
`d₀` decomposition remains in `DoldKan.DegenerateDecomposition` as a convention-specific companion.

@stack 019A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.normalizedMooreComplex.lowerFace

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace projection

/-- The degree-`n` projection from the ambient simplicial object to the source-signed normalized
subobject. -/
@[stacks 019A "source-signed normalized projection component"]
noncomputable def app (U : SimplicialObject A) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶
      (normalizedMooreComplex.lowerFace.obj U).X n :=
  SimplicialObject.normalizedMoore.lowerFace.splitting.projection U n

/-- The normalized inclusion followed by the source-signed projection is the identity. -/
@[reassoc, stacks 019A "source-signed normalized inclusion projection identity"]
theorem inclusion_comp_app (U : SimplicialObject A) (n : ℕ) :
    (SimplicialObject.normalizedMoore.lowerFace.subobject U n).arrow ≫
        app U n = 𝟙 _ := sorry

/-- Source-signed normalized projections are natural in the simplicial object. -/
@[reassoc, stacks 019A "source-signed normalized projection naturality"]
theorem app_naturality {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    f.app (op ⦋n⦌) ≫ app V n =
      app U n ≫ SimplicialObject.normalizedMoore.lowerFace.subobject.map f n := sorry

/-- The source-signed normalized projection components commute with all differentials. -/
@[reassoc, stacks 019A "source-signed normalized projection differential compatibility"]
theorem comm (U : SimplicialObject A) (i j : ℕ) :
    app U i ≫ (normalizedMooreComplex.lowerFace.obj U).d i j =
      ((alternatingFaceMapComplex A).obj U).d i j ≫ app U j := sorry

end projection

/-- The source-signed normalized projection from the alternating-face complex. -/
@[stacks 019A "source-signed normalized projection"]
noncomputable def projection (U : SimplicialObject A) :
    (alternatingFaceMapComplex A).obj U ⟶ normalizedMooreComplex.lowerFace.obj U where
  f := projection.app U
  comm' i j _ := projection.comm U i j

namespace projection

/-- The degree-`n` component of the source-signed normalized projection. -/
@[simp, stacks 019A "source-signed normalized projection component formula"]
theorem f (U : SimplicialObject A) (n : ℕ) :
    (projection U).f n = app U n := sorry

/-- Source-signed normalized projections are natural as chain maps. -/
@[reassoc, stacks 019A "source-signed normalized chain projection naturality"]
theorem naturality {U V : SimplicialObject A} (f : U ⟶ V) :
    (alternatingFaceMapComplex A).map f ≫ projection V =
      projection U ≫ normalizedMooreComplex.lowerFace.map f := sorry

/-- The source-signed normalized projections form a natural transformation. -/
@[stacks 019A "source-signed normalized projection natural transformation"]
noncomputable def natTrans :
    alternatingFaceMapComplex A ⟶ normalizedMooreComplex.lowerFace (A := A) where
  app := projection
  naturality _ _ f := naturality f

/-- The component of the source-signed normalized projection natural transformation. -/
@[simp, stacks 019A "source-signed normalized projection natural component"]
theorem natTrans_app (U : SimplicialObject A) :
    (natTrans (A := A)).app U = projection U := sorry

end projection

namespace degenerate

/-- The complementary projector associated to the source-signed normalized retract. -/
@[stacks 019A "source-signed degenerate projector"]
noncomputable def projector (U : SimplicialObject A) :
    (alternatingFaceMapComplex A).obj U ⟶ (alternatingFaceMapComplex A).obj U :=
  𝟙 _ - projection U ≫ normalizedMooreComplex.lowerFace.inclusion.app U

/-- The degree-`n` component of the source-signed complementary projector. -/
@[simp, stacks 019A "source-signed degenerate projector component"]
theorem projector_f (U : SimplicialObject A) (n : ℕ) :
    (projector U).f n =
      𝟙 _ - projection.app U n ≫
        (SimplicialObject.normalizedMoore.lowerFace.subobject U n).arrow := sorry

/-- The source-signed complementary projector is idempotent. -/
@[stacks 019A "source-signed degenerate projector idempotence"]
theorem projector_comp_self (U : SimplicialObject A) :
    projector U ≫ projector U = projector U := sorry

namespace projection

/-- The source-signed complementary projector factors degreewise through the degenerate subobject. -/
@[stacks 019A "source-signed degenerate projection component factorization"]
theorem app.factors (U : SimplicialObject A) (n : ℕ) :
    (AlgebraicTopology.DoldKan.degenerateSubobject U n).Factors ((projector U).f n) := sorry

/-- The degree-`n` source-signed projection onto the degenerate subobject. -/
@[stacks 019A "source-signed degenerate projection component"]
noncomputable def app (U : SimplicialObject A) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶
      (AlgebraicTopology.DoldKan.degenerateSubobject U n : A) :=
  (AlgebraicTopology.DoldKan.degenerateSubobject U n).factorThru
    ((projector U).f n) (app.factors U n)

/-- The source-signed degenerate projection recovers the complementary projector after inclusion. -/
@[reassoc, stacks 019A "source-signed degenerate projection component formula"]
theorem app_arrow (U : SimplicialObject A) (n : ℕ) :
    app U n ≫ (AlgebraicTopology.DoldKan.degenerateSubobject U n).arrow =
      (projector U).f n := sorry

/-- The source-signed degenerate projection components commute with the degenerate differentials. -/
@[stacks 019A "source-signed degenerate projection differential compatibility"]
theorem comm (U : SimplicialObject A) (i j : ℕ) :
    app U i ≫ (AlgebraicTopology.DoldKan.degenerateComplex U).d i j =
      ((alternatingFaceMapComplex A).obj U).d i j ≫ app U j := sorry

end projection

/-- The source-signed projection from the alternating-face complex to its degenerate subcomplex. -/
@[stacks 019A "source-signed degenerate projection"]
noncomputable def projection (U : SimplicialObject A) :
    (alternatingFaceMapComplex A).obj U ⟶ AlgebraicTopology.DoldKan.degenerateComplex U where
  f := projection.app U
  comm' i j _ := projection.comm U i j

namespace projection

/-- The degree-`n` component of the source-signed degenerate projection. -/
@[simp, stacks 019A "source-signed degenerate projection component projection"]
theorem f (U : SimplicialObject A) (n : ℕ) :
    (degenerate.projection U).f n = app U n := sorry

/-- The source-signed degenerate projection recovers the complementary projector after inclusion. -/
@[reassoc, stacks 019A "source-signed degenerate projection-inclusion formula"]
theorem comp_inclusion (U : SimplicialObject A) :
    degenerate.projection U ≫ AlgebraicTopology.DoldKan.degenerateComplex.ι U =
      projector U := sorry

/-- Source-signed degenerate projections are natural in the simplicial object. -/
@[reassoc, stacks 019A "source-signed degenerate projection naturality"]
theorem naturality {U V : SimplicialObject A} (f : U ⟶ V) :
    (alternatingFaceMapComplex A).map f ≫ degenerate.projection V =
      degenerate.projection U ≫ AlgebraicTopology.DoldKan.degenerateComplex.map f := sorry

/-- The source-signed degenerate projections form a natural transformation. -/
@[stacks 019A "source-signed degenerate projection natural transformation"]
noncomputable def natTrans :
    alternatingFaceMapComplex A ⟶
      AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A) where
  app := degenerate.projection
  naturality _ _ f := naturality f

/-- The component of the source-signed degenerate projection natural transformation. -/
@[simp, stacks 019A "source-signed degenerate projection natural component"]
theorem natTrans_app (U : SimplicialObject A) :
    (natTrans (A := A)).app U = degenerate.projection U := sorry

end projection

end degenerate

namespace decomposition

/-- The source-signed normalized--degenerate projection of the alternating-face complex. -/
@[stacks 019A "source-signed normalized-degenerate decomposition projection"]
noncomputable def hom (U : SimplicialObject A) :
    (alternatingFaceMapComplex A).obj U ⟶
      (normalizedMooreComplex.lowerFace.obj U) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex U :=
  biprod.lift (projection U) (degenerate.projection U)

/-- The source-signed normalized--degenerate reconstruction map. -/
@[stacks 019A "source-signed normalized-degenerate reconstruction map"]
noncomputable def inv (U : SimplicialObject A) :
    (normalizedMooreComplex.lowerFace.obj U) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex U ⟶
      (alternatingFaceMapComplex A).obj U :=
  biprod.desc (normalizedMooreComplex.lowerFace.inclusion.app U)
    (AlgebraicTopology.DoldKan.degenerateComplex.ι U)

/-- The source-signed decomposition projection and reconstruction compose to the identity. -/
@[reassoc, stacks 019A "source-signed normalized-degenerate decomposition inverse law"]
theorem hom_comp_inv (U : SimplicialObject A) :
    hom U ≫ inv U = 𝟙 _ := sorry

/-- The source-signed reconstruction and projection compose to the identity. -/
@[reassoc, stacks 019A "source-signed normalized-degenerate decomposition inverse law"]
theorem inv_comp_hom (U : SimplicialObject A) :
    inv U ≫ hom U = 𝟙 _ := sorry

/-- The alternating-face complex splits into the source-signed normalized and degenerate summands.
-/
@[stacks 019A "source-signed Dold-Kan normalized-degenerate decomposition"]
noncomputable def iso (U : SimplicialObject A) :
    (alternatingFaceMapComplex A).obj U ≅
      (normalizedMooreComplex.lowerFace.obj U) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex U where
  hom := hom U
  inv := inv U
  hom_inv_id := hom_comp_inv U
  inv_hom_id := inv_comp_hom U

/- The following coordinate formulas are kept next to the concrete maps.  They are the stable
   rewriting interface for downstream proofs; users should not unfold the biproduct construction. -/

/-- The forward source-signed decomposition map is the pair of normalized and degenerate projections. -/
@[simp, stacks 019A "source-signed normalized-degenerate decomposition map formula"]
theorem hom_def (U : SimplicialObject A) :
    hom U =
      biprod.lift (projection U) (degenerate.projection U) := sorry

/-- The inverse source-signed decomposition map is induced by the two inclusions. -/
@[simp, stacks 019A "source-signed normalized-degenerate reconstruction map formula"]
theorem inv_def (U : SimplicialObject A) :
    inv U =
      biprod.desc (normalizedMooreComplex.lowerFace.inclusion.app U)
        (AlgebraicTopology.DoldKan.degenerateComplex.ι U) := sorry

/-- The forward map of the objectwise source-signed decomposition is its named projection map. -/
@[simp, stacks 019A "source-signed decomposition forward map"]
theorem iso_hom (U : SimplicialObject A) : (iso U).hom = hom U := sorry

/-- The inverse map of the objectwise source-signed decomposition is its named reconstruction. -/
@[simp, stacks 019A "source-signed decomposition inverse map"]
theorem iso_inv (U : SimplicialObject A) : (iso U).inv = inv U := sorry

/-- The normalized inclusion is the left biproduct coordinate of the source-signed decomposition. -/
@[reassoc, stacks 019A "source-signed normalized inclusion coordinate"]
theorem inclusion_comp_hom (U : SimplicialObject A) :
    normalizedMooreComplex.lowerFace.inclusion.app U ≫ (iso U).hom = biprod.inl := sorry

/-- The normalized projection is the left coordinate of the source-signed decomposition. -/
@[reassoc, stacks 019A "source-signed normalized projection coordinate"]
theorem hom_comp_fst (U : SimplicialObject A) :
    (iso U).hom ≫ biprod.fst = projection U := sorry

/-- The degenerate projection is the right coordinate of the source-signed decomposition. -/
@[reassoc, stacks 019A "source-signed degenerate projection coordinate"]
theorem hom_comp_snd (U : SimplicialObject A) :
    (iso U).hom ≫ biprod.snd = degenerate.projection U := sorry

namespace degenerate.ι

/-- The degenerate inclusion is the right coordinate of the source-signed decomposition. -/
@[reassoc, stacks 019A "source-signed degenerate inclusion coordinate"]
theorem comp_hom (U : SimplicialObject A) :
    AlgebraicTopology.DoldKan.degenerateComplex.ι U ≫ (iso U).hom = biprod.inr := sorry

end degenerate.ι

/-- The inverse decomposition sends the left biproduct inclusion to the normalized inclusion. -/
@[reassoc, stacks 019A "source-signed inverse decomposition normalized coordinate"]
theorem inl_comp_inv (U : SimplicialObject A) :
    biprod.inl ≫ (iso U).inv = normalizedMooreComplex.lowerFace.inclusion.app U := sorry

/-- The inverse decomposition sends the right biproduct inclusion to the degenerate inclusion. -/
@[reassoc, stacks 019A "source-signed inverse decomposition degenerate coordinate"]
theorem inr_comp_inv (U : SimplicialObject A) :
    biprod.inr ≫ (iso U).inv = AlgebraicTopology.DoldKan.degenerateComplex.ι U := sorry

namespace inclusion

/-- The normalized inclusion has zero component in the degenerate summand. -/
@[reassoc, stacks 019A "source-signed normalized inclusion annihilates the degenerate projection"]
theorem comp_degenerateProjection (U : SimplicialObject A) :
    normalizedMooreComplex.lowerFace.inclusion.app U ≫
        degenerate.projection U = 0 := sorry

end inclusion

namespace degenerate.ι

/-- The degenerate inclusion has zero component in the normalized summand. -/
@[reassoc, stacks 019A "source-signed degenerate inclusion annihilates the normalized projection"]
theorem comp_projection (U : SimplicialObject A) :
    AlgebraicTopology.DoldKan.degenerateComplex.ι U ≫ projection U = 0 := sorry

end degenerate.ι

/-- The normalized and degenerate projectors sum to the identity on the alternating-face complex. -/
@[stacks 019A "source-signed normalized-degenerate projector sum"]
theorem projector_sum (U : SimplicialObject A) :
    (projection U ≫ normalizedMooreComplex.lowerFace.inclusion.app U :
        K[U] ⟶ K[U]) +
        (degenerate.projection U ≫
          AlgebraicTopology.DoldKan.degenerateComplex.ι U : K[U] ⟶ K[U]) = 𝟙 _ := sorry

/-- The source-signed normalized inclusion followed by its chain projection is the identity. -/
@[reassoc, stacks 019A "source-signed normalized chain retract law"]
theorem inclusion_comp_projection (U : SimplicialObject A) :
    normalizedMooreComplex.lowerFace.inclusion.app U ≫ projection U =
      𝟙 (normalizedMooreComplex.lowerFace.obj U) := sorry

/-- The functorial projection to the two source-signed summands. -/
@[stacks 019A "source-signed normalized-degenerate decomposition natural projection"]
noncomputable def toSummand :
    alternatingFaceMapComplex A ⟶
      (normalizedMooreComplex.lowerFace (A := A)) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A) :=
  biprod.lift projection.natTrans
    (degenerate.projection.natTrans (A := A))

/-- The functorial reconstruction from the two source-signed summands. -/
@[stacks 019A "source-signed normalized-degenerate decomposition natural reconstruction"]
noncomputable def fromSummand :
    (normalizedMooreComplex.lowerFace (A := A)) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A) ⟶
      alternatingFaceMapComplex A :=
  biprod.desc normalizedMooreComplex.lowerFace.inclusion.natTrans
    (AlgebraicTopology.DoldKan.degenerateComplex.ι.natTrans (C := A))

/-- The source-signed functorial projection and reconstruction compose to the identity. -/
@[stacks 019A "source-signed functorial decomposition inverse law"]
theorem to_comp_from :
    toSummand (A := A) ≫ fromSummand (A := A) = 𝟙 (alternatingFaceMapComplex A) := sorry

/-- The source-signed functorial reconstruction and projection compose to the identity. -/
@[stacks 019A "source-signed functorial decomposition inverse law"]
theorem from_comp_to :
    fromSummand (A := A) ≫ toSummand (A := A) =
      𝟙 ((normalizedMooreComplex.lowerFace (A := A)) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A)) := sorry

/-- The source-signed normalized--degenerate decomposition as a natural isomorphism. -/
@[stacks 019A "source-signed normalized-degenerate decomposition natural isomorphism"]
noncomputable def natIso :
    alternatingFaceMapComplex A ≅
      (normalizedMooreComplex.lowerFace (A := A)) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A) where
  hom := toSummand
  inv := fromSummand
  hom_inv_id := to_comp_from
  inv_hom_id := from_comp_to

/-- Evaluation identifies the functor-category source-signed summands with their objectwise
binary biproduct. -/
@[stacks 019A "source-signed decomposition evaluation comparison"]
noncomputable def evalIso (U : SimplicialObject A) :
    ( ((normalizedMooreComplex.lowerFace (A := A)) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A)).obj U) ≅
      (normalizedMooreComplex.lowerFace.obj U) ⊞
        AlgebraicTopology.DoldKan.degenerateComplex U :=
  CategoryTheory.Limits.evalBiprodIso (normalizedMooreComplex.lowerFace (A := A))
    (AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A)) U

/-- The evaluated source-signed natural decomposition is the objectwise decomposition. -/
@[stacks 019A "source-signed decomposition component"]
theorem natIso.app (U : SimplicialObject A) :
    (natIso (A := A)).app U ≪≫ evalIso U = iso U := sorry

/-- The forward evaluated natural decomposition is the objectwise forward decomposition map. -/
@[stacks 019A "forward source-signed decomposition component"]
theorem natIso.hom_app (U : SimplicialObject A) :
    (natIso (A := A)).hom.app U ≫ (evalIso U).hom = (iso U).hom := sorry

/-- The inverse of the evaluated source-signed decomposition is the inverse evaluation bridge
followed by the inverse functor-category component. -/
@[stacks 019A "inverse source-signed decomposition component"]
theorem natIso.inv_app (U : SimplicialObject A) :
    (evalIso U).inv ≫ (natIso (A := A)).inv.app U = (iso U).inv := sorry

/-- The normalized coordinate of the functorial source-signed decomposition is `projection`. -/
@[reassoc, stacks 019A "source-signed normalized coordinate of the functorial decomposition"]
theorem toSummand.app_fst (U : SimplicialObject A) :
    (toSummand (A := A)).app U ≫
      ((biprod.fst :
        (normalizedMooreComplex.lowerFace (A := A)) ⊞
          AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A) ⟶
        normalizedMooreComplex.lowerFace (A := A)).app U) = projection U := sorry

/-- The degenerate coordinate of the functorial source-signed decomposition is the source-signed
degenerate projection. -/
@[reassoc, stacks 019A "source-signed degenerate coordinate of the functorial decomposition"]
theorem toSummand.app_snd (U : SimplicialObject A) :
    (toSummand (A := A)).app U ≫
      ((biprod.snd :
        (normalizedMooreComplex.lowerFace (A := A)) ⊞
          AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A) ⟶
        AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A)).app U) =
      degenerate.projection U := sorry

/-- The functorial reconstruction restricts to the normalized inclusion on the left summand. -/
@[reassoc, stacks 019A "source-signed normalized coordinate of the functorial reconstruction"]
theorem fromSummand.inl_app (U : SimplicialObject A) :
    ((biprod.inl : normalizedMooreComplex.lowerFace (A := A) ⟶
        (normalizedMooreComplex.lowerFace (A := A)) ⊞
          AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A)).app U) ≫
      (fromSummand (A := A)).app U = normalizedMooreComplex.lowerFace.inclusion.app U := sorry

/-- The functorial reconstruction restricts to the degenerate inclusion on the right summand. -/
@[reassoc, stacks 019A "source-signed degenerate coordinate of the functorial reconstruction"]
theorem fromSummand.inr_app (U : SimplicialObject A) :
    ((biprod.inr : AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A) ⟶
        (normalizedMooreComplex.lowerFace (A := A)) ⊞
          AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A)).app U) ≫
      (fromSummand (A := A)).app U = AlgebraicTopology.DoldKan.degenerateComplex.ι U := sorry

end decomposition

/-- The natural source-signed normalized inclusion followed by the natural projection is the
identity. -/
@[reassoc, stacks 019A "natural source-signed normalized inclusion-projection retraction"]
theorem inclusion.natTrans_comp_projection :
    normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A) ≫
        projection.natTrans (A := A) =
      𝟙 (normalizedMooreComplex.lowerFace (A := A)) := sorry

namespace inclusion

/-- The natural source-signed normalized inclusion, equipped with its natural retraction. -/
@[stacks 019A "natural source-signed normalized split monomorphism"]
def splitMono :
    SplitMono (normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A)) where
  retraction := projection.natTrans (A := A)
  id := inclusion.natTrans_comp_projection (A := A)

/-- The source-signed normalized inclusion at `U`, equipped with its canonical chain
retraction. -/
@[stacks 019A "source-signed normalized component split monomorphism"]
def appSplitMono (U : SimplicialObject A) :
    SplitMono (normalizedMooreComplex.lowerFace.inclusion.app U) where
  retraction := projection U
  id := decomposition.inclusion_comp_projection U

/-- The natural source-signed normalized inclusion is available to typeclass search as split. -/
@[instance, stacks 019A "natural source-signed normalized split monomorphism instance"]
theorem isSplitMono :
    IsSplitMono (normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A)) := sorry

/-- Every component of the source-signed normalized inclusion is available to typeclass search as
split. -/
@[instance, stacks 019A "source-signed normalized component split monomorphism instance"]
theorem appIsSplitMono (U : SimplicialObject A) :
    IsSplitMono (normalizedMooreComplex.lowerFace.inclusion.app U) := sorry

end inclusion

namespace projection

/-- The natural source-signed normalized projection, equipped with its natural section. -/
@[stacks 019A "natural source-signed normalized split epimorphism"]
def splitEpi : SplitEpi (projection.natTrans (A := A)) where
  section_ := normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A)
  id := inclusion.natTrans_comp_projection (A := A)

/-- The source-signed normalized projection at `U`, equipped with its canonical chain section. -/
@[stacks 019A "source-signed normalized component split epimorphism"]
def appSplitEpi (U : SimplicialObject A) : SplitEpi (projection U) where
  section_ := normalizedMooreComplex.lowerFace.inclusion.app U
  id := decomposition.inclusion_comp_projection U

/-- The natural source-signed normalized projection is available to typeclass search as split. -/
@[instance, stacks 019A "natural source-signed normalized split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (projection.natTrans (A := A)) := sorry

/-- Every component of the source-signed normalized projection is available to typeclass search as
split. -/
@[instance, stacks 019A "source-signed normalized component split epimorphism instance"]
theorem appIsSplitEpi (U : SimplicialObject A) :
    IsSplitEpi (projection U) := sorry

end projection

/-- The natural degenerate inclusion followed by the natural source-signed degenerate projection is
the identity. -/
@[reassoc, stacks 019A "natural source-signed degenerate inclusion-projection retraction"]
theorem degenerate.ι.natTrans_comp_projection :
    AlgebraicTopology.DoldKan.degenerateComplex.ι.natTrans (C := A) ≫
        degenerate.projection.natTrans (A := A) =
      𝟙 (AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A)) := sorry

namespace degenerate.projection

/-- The degenerate inclusion followed by the source-signed degenerate projection is the identity. -/
@[reassoc, stacks 019A "source-signed degenerate inclusion-projection identity"]
theorem inclusion_comp (U : SimplicialObject A) :
    AlgebraicTopology.DoldKan.degenerateComplex.ι U ≫ degenerate.projection U = 𝟙 _ := sorry

/-- The natural source-signed degenerate projection, equipped with its natural section. -/
@[stacks 019A "natural source-signed degenerate split epimorphism"]
def splitEpi : SplitEpi (degenerate.projection.natTrans (A := A)) where
  section_ := AlgebraicTopology.DoldKan.degenerateComplex.ι.natTrans (C := A)
  id := degenerate.ι.natTrans_comp_projection (A := A)

/-- The source-signed degenerate projection at `U`, equipped with its canonical chain section. -/
@[stacks 019A "source-signed degenerate component split epimorphism"]
def appSplitEpi (U : SimplicialObject A) : SplitEpi (degenerate.projection U) where
  section_ := AlgebraicTopology.DoldKan.degenerateComplex.ι U
  id := inclusion_comp U

/-- The natural source-signed degenerate projection is available to typeclass search as split. -/
@[instance, stacks 019A "natural source-signed degenerate split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (degenerate.projection.natTrans (A := A)) := sorry

/-- Every component of the source-signed degenerate projection is available to typeclass search as
split. -/
@[instance, stacks 019A "source-signed degenerate component split epimorphism instance"]
theorem appIsSplitEpi (U : SimplicialObject A) :
    IsSplitEpi (degenerate.projection U) := sorry

end degenerate.projection

namespace degenerate.ι

/-- The source-signed degenerate inclusion with the retraction supplied by the complementary
projection. -/
@[stacks 019A "source-signed degenerate inclusion split monomorphism"]
def splitMono :
    SplitMono (AlgebraicTopology.DoldKan.degenerateComplex.ι.natTrans (C := A)) :=
  degenerate.projection.splitEpi (A := A) |>.splitMono

/-- The source-signed degenerate inclusion at `U` with its complementary projection retraction. -/
@[stacks 019A "source-signed degenerate component split monomorphism"]
def appSplitMono (U : SimplicialObject A) :
    SplitMono (AlgebraicTopology.DoldKan.degenerateComplex.ι U) :=
  degenerate.projection.appSplitEpi U |>.splitMono

/-- The natural source-signed degenerate inclusion is available to typeclass search as split. -/
@[instance, stacks 019A "source-signed degenerate split monomorphism instance"]
theorem isSplitMono :
    IsSplitMono (AlgebraicTopology.DoldKan.degenerateComplex.ι.natTrans (C := A)) := sorry

/-- Every component of the source-signed degenerate inclusion is available to typeclass search as
split. -/
@[instance, stacks 019A "source-signed degenerate component split monomorphism instance"]
theorem appIsSplitMono (U : SimplicialObject A) :
    IsSplitMono (AlgebraicTopology.DoldKan.degenerateComplex.ι U) := sorry

end degenerate.ι

namespace decomposition

/-- The four structural maps of the source-signed normalized--degenerate decomposition form a
binary bicone with vertex the alternating-face complex. -/
@[stacks 019A "source-signed normalized-degenerate binary bicone"]
noncomputable def bicone (U : SimplicialObject A) :
    BinaryBicone (normalizedMooreComplex.lowerFace.obj U)
      (AlgebraicTopology.DoldKan.degenerateComplex U) where
  pt := (alternatingFaceMapComplex A).obj U
  fst := projection U
  snd := degenerate.projection U
  inl := normalizedMooreComplex.lowerFace.inclusion.app U
  inr := AlgebraicTopology.DoldKan.degenerateComplex.ι U
  inl_fst := inclusion_comp_projection U
  inl_snd := inclusion.comp_degenerateProjection U
  inr_fst := degenerate.ι.comp_projection U
  inr_snd := degenerate.projection.inclusion_comp U

/-- The source-signed normalized--degenerate binary bicone is a biproduct decomposition. -/
@[stacks 019A "source-signed normalized-degenerate binary biproduct"]
noncomputable def isBilimit (U : SimplicialObject A) :
    (bicone U).IsBilimit :=
  isBinaryBilimitOfTotal (bicone U) (projector_sum U)

/-- The natural transformation-level form of the source-signed normalized--degenerate bicone. -/
@[stacks 019A "source-signed normalized-degenerate natural binary bicone"]
noncomputable def natBicone :
    BinaryBicone (normalizedMooreComplex.lowerFace (A := A))
      (AlgebraicTopology.DoldKan.degenerateComplex.functor (C := A)) where
  pt := alternatingFaceMapComplex A
  fst := projection.natTrans (A := A)
  snd := degenerate.projection.natTrans (A := A)
  inl := normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A)
  inr := AlgebraicTopology.DoldKan.degenerateComplex.ι.natTrans (C := A)
  inl_fst := NatTrans.ext (funext (fun U => inclusion_comp_projection U))
  inl_snd := NatTrans.ext (funext (fun U => inclusion.comp_degenerateProjection U))
  inr_fst := NatTrans.ext (funext (fun U => degenerate.ι.comp_projection U))
  inr_snd := NatTrans.ext (funext (fun U => degenerate.projection.inclusion_comp U))

/-- The natural source-signed normalized--degenerate bicone is a binary biproduct. -/
@[stacks 019A "source-signed normalized-degenerate natural binary biproduct"]
noncomputable def natIsBilimit :
    (natBicone (A := A)).IsBilimit :=
  isBinaryBilimitOfTotal (natBicone (A := A))
    (NatTrans.ext (funext (fun U => projector_sum U)))

end decomposition

namespace inclusion

/-- The source-signed degenerate summand as the cokernel of the normalized inclusion. -/
@[stacks 019A "source-signed normalized inclusion cokernel comparison"]
noncomputable def cokernelIso (U : SimplicialObject A) :
    cokernel (normalizedMooreComplex.lowerFace.inclusion.app U) ≅
      AlgebraicTopology.DoldKan.degenerateComplex U :=
  colimit.isoColimitCocone
    ⟨(decomposition.bicone U).inlCokernelCofork,
      BinaryBicone.isColimitInlCokernelCofork
        (decomposition.isBilimit U).isColimit⟩

/-- The source-signed degenerate projection is the quotient coordinate of the normalized
inclusion. -/
@[simp, reassoc, stacks 019A "source-signed normalized inclusion cokernel projection"]
theorem cokernelIso_hom_fac (U : SimplicialObject A) :
    cokernel.π (normalizedMooreComplex.lowerFace.inclusion.app U) ≫
        (cokernelIso U).hom = degenerate.projection U := sorry

end inclusion

namespace degenerate.ι

/-- The source-signed normalized complex as the quotient by the degenerate subcomplex. -/
@[stacks 019A "source-signed quotient by the degenerate subcomplex"]
noncomputable def cokernelIso (U : SimplicialObject A) :
    cokernel (AlgebraicTopology.DoldKan.degenerateComplex.ι U) ≅
      normalizedMooreComplex.lowerFace.obj U :=
  colimit.isoColimitCocone
    ⟨(decomposition.bicone U).inrCokernelCofork,
      BinaryBicone.isColimitInrCokernelCofork
        (decomposition.isBilimit U).isColimit⟩

/-- The normalized projection is the quotient coordinate of the degenerate inclusion. -/
@[simp, reassoc, stacks 019A "source-signed degenerate inclusion cokernel projection"]
theorem cokernelIso_hom_fac (U : SimplicialObject A) :
    cokernel.π (AlgebraicTopology.DoldKan.degenerateComplex.ι U) ≫
        (cokernelIso U).hom =
      AlgebraicTopology.normalizedMooreComplex.lowerFace.projection U := sorry

end degenerate.ι

namespace projection

/-- The source-signed degenerate complex as the kernel of the normalized projection. -/
@[stacks 019A "source-signed normalized projection kernel comparison"]
noncomputable def kernelIso (U : SimplicialObject A) :
    kernel (projection U) ≅ AlgebraicTopology.DoldKan.degenerateComplex U :=
  limit.isoLimitCone
    ⟨(decomposition.bicone U).fstKernelFork,
      BinaryBicone.isLimitFstKernelFork (decomposition.isBilimit U).isLimit⟩

/-- The degenerate inclusion is the kernel coordinate of the normalized projection. -/
@[simp, reassoc, stacks 019A "source-signed normalized projection kernel inclusion"]
theorem kernelIso_inv_fac (U : SimplicialObject A) :
    (kernelIso U).inv ≫ kernel.ι (projection U) =
      AlgebraicTopology.DoldKan.degenerateComplex.ι U := sorry

end projection

namespace degenerate.projection

/-- The source-signed normalized complex as the kernel of the degenerate projection. -/
@[stacks 019A "source-signed degenerate projection kernel comparison"]
noncomputable def kernelIso (U : SimplicialObject A) :
    kernel (degenerate.projection U) ≅
      normalizedMooreComplex.lowerFace.obj U :=
  limit.isoLimitCone
    ⟨(decomposition.bicone U).sndKernelFork,
      BinaryBicone.isLimitSndKernelFork (decomposition.isBilimit U).isLimit⟩

/-- The normalized inclusion is the kernel coordinate of the degenerate projection. -/
@[simp, reassoc, stacks 019A "source-signed degenerate projection kernel inclusion"]
theorem kernelIso_inv_fac (U : SimplicialObject A) :
    (kernelIso U).inv ≫ kernel.ι (degenerate.projection U) =
      normalizedMooreComplex.lowerFace.inclusion.app U := sorry

end degenerate.projection

end AlgebraicTopology.normalizedMooreComplex.lowerFace
