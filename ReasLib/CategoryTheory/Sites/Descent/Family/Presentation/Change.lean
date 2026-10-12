/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Changing chosen presentations of family descent data

This leaf records the direct equivalence between two chosen overlap presentations and its stable
object, morphism, and overlap-morphism computation API.  The basic chosen/canonical conversion
API is owned by `Descent.Family.Presentation`.
-/

@[expose] public section

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C}

namespace DescentDatum

/-- Change the chosen pairwise and triple overlap presentation of family descent data. The
representation-independent category is the intermediate owner. -/
noncomputable def Chosen.changePresentation
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation) :
    Chosen hc P ≌ Chosen hc Q :=
  (Chosen.equivalence hc P).trans (Chosen.equivalence hc Q).symm

/-- The forward functor changing presentations factors through canonical descent data. -/
theorem Chosen.changePresentation_functor
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation) :
    (Chosen.changePresentation hc P Q).functor =
      Chosen.toCanonical hc P ⋙ Chosen.fromCanonical hc Q := sorry

/-- The inverse functor changing presentations factors through canonical descent data. -/
theorem Chosen.changePresentation_inverse
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation) :
    (Chosen.changePresentation hc P Q).inverse =
      Chosen.toCanonical hc Q ⋙ Chosen.fromCanonical hc P := sorry

/-- Changing overlap presentations retains every object over a family member. -/
@[simp]
theorem Chosen.changePresentation_obj_obj
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation)
    (D : Chosen hc P) (i : 𝒰.index) :
    ((Chosen.changePresentation hc P Q).functor.obj D).obj i = D.obj i := sorry

/-- Changing overlap presentations retains every component of a descent-data morphism. -/
@[simp]
theorem Chosen.changePresentation_map_hom
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation)
    {D E : Chosen hc P} (φ : D ⟶ E) (i : 𝒰.index) :
    ((Chosen.changePresentation hc P Q).functor.map φ).hom i = φ.hom i := sorry

/-- After changing presentations, the new chosen overlap morphism is obtained by extending the old
one to the overlap cone selected by the new presentation. -/
@[simp]
theorem Chosen.changePresentation_obj_hom
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation)
    (D : Chosen hc P) (i j : 𝒰.index) :
    ((Chosen.changePresentation hc P Q).functor.obj D).hom i j =
      Pseudofunctor.DescentData'.pullHom' D.hom
        (Q.overlapMap i j) (Q.fst i j) (Q.snd i j)
        (Q.fst_hom i j) (Q.snd_hom i j) := sorry

/-- The inverse change of presentation also retains every family object. -/
@[simp]
theorem Chosen.changePresentation_inverse_obj_obj
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation)
    (D : Chosen hc Q) (i : 𝒰.index) :
    ((Chosen.changePresentation hc P Q).inverse.obj D).obj i = D.obj i := sorry

/-- The inverse change of presentation retains every morphism component. -/
@[simp]
theorem Chosen.changePresentation_inverse_map_hom
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation)
    {D E : Chosen hc Q} (φ : D ⟶ E) (i : 𝒰.index) :
    ((Chosen.changePresentation hc P Q).inverse.map φ).hom i = φ.hom i := sorry

/-- The inverse change evaluates the extended descent morphism on the overlap selected by the
original presentation. -/
@[simp]
theorem Chosen.changePresentation_inverse_obj_hom
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P Q : 𝒰.OverlapPresentation)
    (D : Chosen hc Q) (i j : 𝒰.index) :
    ((Chosen.changePresentation hc P Q).inverse.obj D).hom i j =
      Pseudofunctor.DescentData'.pullHom' D.hom
        (P.overlapMap i j) (P.fst i j) (P.snd i j)
        (P.fst_hom i j) (P.snd_hom i j) := sorry

end DescentDatum

end CategoryTheory
