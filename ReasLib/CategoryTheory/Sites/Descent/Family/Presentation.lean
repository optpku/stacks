/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.DescentDatum
public import ReasLib.CategoryTheory.Sites.Descent.Family.Overlap.Choice
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen-overlap presentations of family descent data

`DescentDatum` is the canonical, representation-independent owner.  When a consumer needs the
literal chosen pairwise/triple pullback presentation used by the Stacks text, `DescentDatum.Chosen`
packages mathlib's `DescentData'`. The comparison is mathlib's canonical equivalence; the two
conversion functors below are only its projections.
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

/-- The literal chosen-overlap presentation of descent data for a family. -/
@[stacks 026B "chosen-overlap presentation of family descent data"]
abbrev Chosen
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation) :=
  (hc.toPseudofunctor).DescentData' P.pairwise P.triple

/-- The canonical equivalence between chosen-overlap and representation-independent descent data. -/
@[stacks 026B "chosen-overlap descent-data equivalence"]
noncomputable abbrev Chosen.equivalence
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation) :
    Chosen hc P ≌ DescentDatum hc 𝒰 :=
  Pseudofunctor.DescentData'.descentDataEquivalence
    hc.toPseudofunctor P.pairwise P.triple

/-- The canonical conversion from the chosen-overlap presentation to `DescentDatum`. -/
@[stacks 026B "chosen-overlap to canonical descent-data functor"]
noncomputable abbrev Chosen.toCanonical
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation) :
    Chosen hc P ⥤ DescentDatum hc 𝒰 :=
  (Chosen.equivalence hc P).functor

/-- The chosen-overlap presentation functor inverse to `Chosen.toCanonical` at the data level. -/
@[stacks 026B "canonical to chosen-overlap descent-data functor"]
noncomputable abbrev Chosen.fromCanonical
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation) :
    DescentDatum hc 𝒰 ⥤ Chosen hc P :=
  (Chosen.equivalence hc P).inverse

/-- The canonical conversion retains the object over every member of the family. -/
@[simp, stacks 026B "object readout of chosen-overlap to canonical conversion"]
theorem Chosen.toCanonical_obj_obj
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation)
    (D : Chosen hc P) (i : 𝒰.index) :
    ((Chosen.toCanonical hc P).obj D).obj i = D.obj i := sorry

/-- The canonical conversion retains every component of a morphism of chosen descent data. -/
@[simp, stacks 026B "morphism readout of chosen-overlap to canonical conversion"]
theorem Chosen.toCanonical_map_hom
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation)
    {D E : Chosen hc P} (φ : D ⟶ E) (i : 𝒰.index) :
    ((Chosen.toCanonical hc P).map φ).hom i = φ.hom i := sorry

/-- The canonical conversion extends a chosen-overlap morphism to an arbitrary compatible cone. -/
@[stacks 026B "comparison readout of chosen-overlap to canonical conversion"]
theorem Chosen.toCanonical_obj_hom
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation)
    (D : Chosen hc P) {Y : C} (q : Y ⟶ U) {i j : 𝒰.index}
    (f₁ : Y ⟶ (𝒰.obj i).left) (f₂ : Y ⟶ (𝒰.obj j).left)
    (hf₁ : f₁ ≫ (𝒰.obj i).hom = q) (hf₂ : f₂ ≫ (𝒰.obj j).hom = q) :
    ((Chosen.toCanonical hc P).obj D).hom q f₁ f₂ hf₁ hf₂ =
      Pseudofunctor.DescentData'.pullHom' D.hom q f₁ f₂ hf₁ hf₂ := sorry

/-- Passing from canonical descent data to a chosen presentation retains each family object. -/
@[simp, stacks 026B "object readout of canonical to chosen-overlap conversion"]
theorem Chosen.fromCanonical_obj_obj
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation)
    (D : DescentDatum hc 𝒰) (i : 𝒰.index) :
    ((Chosen.fromCanonical hc P).obj D).obj i = D.obj i := sorry

/-- Passing from canonical descent data to a chosen presentation retains morphism components. -/
@[simp, stacks 026B "morphism readout of canonical to chosen-overlap conversion"]
theorem Chosen.fromCanonical_map_hom
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation)
    {D E : DescentDatum hc 𝒰} (φ : D ⟶ E) (i : 𝒰.index) :
    ((Chosen.fromCanonical hc P).map φ).hom i = φ.hom i := sorry

/-- In a chosen presentation, the overlap morphism is the canonical descent morphism evaluated on
the selected overlap cone. -/
@[simp, stacks 026B "comparison readout of canonical to chosen-overlap conversion"]
theorem Chosen.fromCanonical_obj_hom
    (hc : Functor.Cleavage p)
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} (P : 𝒰.OverlapPresentation)
    (D : DescentDatum hc 𝒰) (i j : 𝒰.index) :
    ((Chosen.fromCanonical hc P).obj D).hom i j =
      D.hom (P.overlapMap i j) (P.fst i j) (P.snd i j)
        (P.fst_hom i j) (P.snd_hom i j) := sorry

end DescentDatum

end CategoryTheory
