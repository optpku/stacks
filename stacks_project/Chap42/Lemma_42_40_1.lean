module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ExactSequence

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Theory

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
variable (classes : Theory δ p) (E F : X.Modules) (r : ℕ)
variable [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
variable [hF : Scheme.Modules.IsFiniteLocallyFreeOfRank (r - 1) F]
variable (ι : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E) (q : E ⟶ F)
variable (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)

/- Lemma 42.40.1 (1): In a short exact sequence `0 ⟶ 𝒪_X ⟶ E ⟶ F ⟶ 0`
with `E` of rank `r` and `F` of rank `r - 1`, the top Chern component of `E` vanishes. -/
@[stacks 02UG] #check
  (AlgebraicGeometry.ChernClass.Theory.top_eq_zero_of_unit_shortExact
    (δ := δ) (p := p) (classes := classes) (E := E) (F := F) (r := r)
    (ι := ι) (q := q) (hzero := hzero) (hshort := hshort) :
      classes.component E r = 0)

/- Lemma 42.40.1 (2): In a short exact sequence `0 ⟶ 𝒪_X ⟶ E ⟶ F ⟶ 0`
with `E` of rank `r` and `F` of rank `r - 1`, the Chern components of `E` and `F`
agree in every degree below `r`. -/
@[stacks 02UG] #check
  (AlgebraicGeometry.ChernClass.Theory.component_eq_of_unit_shortExact
    (δ := δ) (p := p) (classes := classes) (E := E) (F := F) (r := r)
    (ι := ι) (q := q) (hzero := hzero) (hshort := hshort) :
      ∀ (j : ℕ), j < r → classes.component E j = classes.component F j)

end AlgebraicGeometry.ChernClass.Theory
