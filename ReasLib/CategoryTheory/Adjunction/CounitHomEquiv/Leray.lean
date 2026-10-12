/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.CounitHomEquiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom equivalences from a counit locus and a Leray comparison

Two adjunction Hom equivalences compose with a Leray isomorphism to identify maps after a
left adjoint with maps between derived sections.  The construction is independent of any
particular site presentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe vA vB vE uA uB uE

namespace CategoryTheory.Adjunction.CounitLeray

variable {A : Type uA} {B : Type uB} {E : Type uE}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vE} E]
variable {L : E ⥤ A} {R : A ⥤ E} (sectionsAdj : L ⊣ R)
variable (P : ObjectProperty A) (hP : P ≤ sectionsAdj.counitIsoProperty)
variable {F : A ⥤ B} {G : B ⥤ A} (changeAdj : F ⊣ G)
variable (Rtau : B ⥤ E) (leray : Rtau ≅ G ⋙ R)

/-- Lemma 21.43.13 (0H0T): the topology-change adjunction, the sections equivalence on
the counit locus, and the Leray comparison give the canonical local Hom equivalence. -/
@[stacks 0H0T]
noncomputable abbrev homEquiv (K : P.FullSubcategory) (M : B) :
    (F.obj K.obj ⟶ M) ≃ (R.obj K.obj ⟶ Rtau.obj M) :=
  (changeAdj.homEquiv K.obj M).trans
    ((sectionsAdj.homEquiv_of_counitIsoOn P hP K (G.obj M)).trans
      (Iso.homCongr (Iso.refl (R.obj K.obj)) (leray.app M).symm))

/-- The forward local Hom equivalence applies the two adjunction bijections and then the
inverse Leray comparison. -/
@[simp, stacks 0H0T "forward local Hom comparison"]
theorem homEquiv_apply (K : P.FullSubcategory) (M : B) (f : F.obj K.obj ⟶ M) :
    homEquiv sectionsAdj P hP changeAdj Rtau leray K M f =
      sectionsAdj.homEquiv (R.obj K.obj) (G.obj M)
          (sectionsAdj.counit.app K.obj ≫ changeAdj.homEquiv K.obj M f) ≫
        (leray.app M).inv := sorry

/-- The inverse local Hom equivalence first transports across Leray and then applies the
inverse sections and topology-change adjunction bijections. -/
@[simp, stacks 0H0T "inverse local Hom comparison"]
theorem homEquiv_symm_apply (K : P.FullSubcategory) (M : B)
    (g : R.obj K.obj ⟶ Rtau.obj M) :
    (homEquiv sectionsAdj P hP changeAdj Rtau leray K M).symm g =
      (changeAdj.homEquiv K.obj M).symm
        ((sectionsAdj.homEquiv_of_counitIsoOn P hP K (G.obj M)).symm
          (g ≫ (leray.app M).hom)) := sorry

end CategoryTheory.Adjunction.CounitLeray
