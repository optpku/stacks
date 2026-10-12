/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap76.Lemma_76_7_6_Comparison
public import stacks_project.Chap76.Lemma_76_7_10_Conormal
public import stacks_project.Chap76.Lemma_76_7_11_Retraction

/-!
# Splittings of conormal sequences of immersions of algebraic spaces

Retractions of an immersion over a base split its canonical
conormal-differentials complex. The same condition on étale scheme charts
gives an étale-local splitting. If `r` is a left inverse over the base, the
section of `i^* Ω_{X/B} ⟶ Ω_{Z/B}` is the pullback `i^* c_r`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials

variable {S : Scheme.{u}} {B X Z : AlgebraicSpace S}
variable (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ B)

/-- The section `i^* c_r : Ω_{Z/B} ⟶ i^* Ω_{X/B}` obtained by pulling back the
Lemma 76.7.6 comparison of a retraction `r` over `B`. -/
def sectionOfRetraction (r : X ⟶ Z) (hr : i ≫ r = 𝟙 Z)
    (hrB : r ≫ i ≫ f = f) :
    relativeDifferentials (i ≫ f) ⟶
      (Modules.pullback i).obj (relativeDifferentials f) :=
  (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app
      (relativeDifferentials (i ≫ f)) ≫
    (eqToIso (congrArg Modules.pullback hr)).inv.app
      (relativeDifferentials (i ≫ f)) ≫
    (Modules.pullbackComp i r).inv.app (relativeDifferentials (i ≫ f)) ≫
    (Modules.pullback i).map
      (Hom.Differentials.comparison r (𝟙 B) (i ≫ f) f
        (hrB.trans (Category.comp_id f).symm))

/-- `sectionOfRetraction` is the composite of `modulesPullbackId`, transport
along `i ≫ r = 𝟙 Z`, `pullbackComp`, and `i^* c_r`. -/
theorem sectionOfRetraction_spec (r : X ⟶ Z) (hr : i ≫ r = 𝟙 Z)
    (hrB : r ≫ i ≫ f = f) :
    sectionOfRetraction i f r hr hrB =
      (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app
          (relativeDifferentials (i ≫ f)) ≫
        (eqToIso (congrArg Modules.pullback hr)).inv.app
          (relativeDifferentials (i ≫ f)) ≫
        (Modules.pullbackComp i r).inv.app (relativeDifferentials (i ≫ f)) ≫
        (Modules.pullback i).map
          (Hom.Differentials.comparison r (𝟙 B) (i ≫ f) f
            (hrB.trans (Category.comp_id f).symm)) :=
  sorry

/-- The pulled comparison `i^* c_r` is a section of
`i^* Ω_{X/B} ⟶ Ω_{Z/B}`. -/
theorem sectionOfRetraction_comp_comparison (r : X ⟶ Z) (hr : i ≫ r = 𝟙 Z)
    (hrB : r ≫ i ≫ f = f) :
    sectionOfRetraction i f r hr hrB ≫ comparison i f =
      𝟙 (relativeDifferentials (i ≫ f)) :=
  sorry

/-- The canonical conormal-differentials complex of an immersion is split on
étale scheme charts covering the images of all source points. -/
def IsEtaleLocallySplit : Prop :=
  ∀ z : Points Z, ∃ (U : Over S) (φ : ofOver U ⟶ X),
    Etale φ ∧ Points.map i z ∈ Set.range (Points.map φ) ∧
      Nonempty ((complex (pullback.snd i φ) (φ ≫ f)).Splitting)

/-- Étale-local splitting of the canonical conormal-differentials complex is
equivalent to the existence of a splitting on an étale scheme chart covering
the image of every source point. -/
theorem isEtaleLocallySplit_iff :
    IsEtaleLocallySplit i f ↔
      ∀ z : Points Z, ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ Points.map i z ∈ Set.range (Points.map φ) ∧
          Nonempty ((complex (pullback.snd i φ) (φ ≫ f)).Splitting) :=
  Iff.rfl

/-- A retraction of an immersion over a base splits its canonical
conormal-differentials complex. -/
theorem complex_splitting_of_hasRetraction (h : HasRetractionOver i f) :
    Nonempty ((complex i f).Splitting) :=
  sorry

/-- Étale-locally defined retractions of an immersion over a base yield
étale-local splittings of its canonical conormal-differentials complex. -/
theorem etaleLocallySplit_of_etaleLocallyHasRetraction
    (h : EtaleLocallyHasRetractionOver i f) :
    IsEtaleLocallySplit i f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials
