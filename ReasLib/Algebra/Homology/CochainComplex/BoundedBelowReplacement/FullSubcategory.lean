/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement
public import Mathlib.Algebra.Homology.FullSubcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise Properties as Complexes in Full Subcategories

A bounded-below complex whose terms satisfy an object property can equivalently be viewed as a
bounded-below complex in the corresponding full subcategory.  This file exposes the canonical
forward functor and its computation API.  It is property-neutral, so injective, projective, and
other termwise conditions can share the same construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CochainComplex.Plus.TermsIn

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Lift a bounded-below termwise-`P` complex degreewise to the full subcategory determined by
`P`, before retaining its bounded-below support. -/
@[stacks 05TW "termwise-property full-subcategory complex"]
noncomputable abbrev liftedFunctor (P : ObjectProperty C) :
    TermsIn P ⥤ CochainComplex P.FullSubcategory ℤ :=
  HomologicalComplex.liftFunctorObjectProperty P (ι P) (fun K n ↦ K.property n)

/-- The degreewise lift of a bounded-below termwise-`P` complex is still bounded below in the
full subcategory. -/
@[stacks 05TW "termwise-property full-subcategory complex"]
theorem liftedFunctor_obj_plus (P : ObjectProperty C) (K : TermsIn P) :
    CochainComplex.plus P.FullSubcategory ((liftedFunctor P).obj K) := sorry

/-- Regard a bounded-below complex whose terms satisfy `P` as a bounded-below complex in the
full subcategory `P.FullSubcategory`. -/
@[stacks 05TW "bounded-below termwise-property full-subcategory view"]
noncomputable def toFullSubcategory (P : ObjectProperty C) :
    TermsIn P ⥤ CochainComplex.Plus P.FullSubcategory :=
  ObjectProperty.lift _ (liftedFunctor P) (liftedFunctor_obj_plus P)

namespace toFullSubcategory

/-- The object in degree `n` of the full-subcategory view has the original term as its
underlying object. -/
@[simp, stacks 05TW "bounded-below termwise-property full-subcategory view"]
theorem obj_obj_X (P : ObjectProperty C) (K : TermsIn P) (n : ℤ) :
    (((toFullSubcategory P).obj K).obj.X n).obj = K.obj.obj.X n := sorry

/-- The differential of the full-subcategory view has the original differential as its
underlying morphism. -/
@[simp, stacks 05TW "bounded-below termwise-property full-subcategory view"]
theorem obj_obj_d (P : ObjectProperty C) (K : TermsIn P) (i j : ℤ) :
    (((toFullSubcategory P).obj K).obj.d i j).hom = K.obj.obj.d i j := sorry

/-- A morphism in the full-subcategory view has the original cochain map component as its
underlying morphism. -/
@[simp, stacks 05TW "bounded-below termwise-property full-subcategory view"]
theorem map_hom_f (P : ObjectProperty C) {K L : TermsIn P} (f : K ⟶ L) (n : ℤ) :
    (((toFullSubcategory P).map f).hom.f n).hom = f.hom.hom.f n := sorry

end toFullSubcategory

end CochainComplex.Plus.TermsIn
