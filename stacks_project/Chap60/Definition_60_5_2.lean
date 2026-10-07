module

public import stacks_project.Chap60.Definition_60_5_2_Thickening
public import stacks_project.Chap60.Definition_60_5_2_Category
import StacksCheckRecall

@[expose] public section

universe u v w

open CategoryTheory

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))
variable {X Y : DividedPowerThickening p A I γ C f hIC h_pC}

/- Definition 60.5.2 (1): a divided power thickening of C over the fixed setup
(A, I, γ) consists of a divided-power A-algebra B, with p nilpotent in B,
together with a map C → B ⧸ J making the quotient square commute. -/
@[stacks 07HM] #check
  (DividedPowerThickening.{u, v, w} p A I γ C f hIC h_pC :
    Type (max (max u v) (w + 1)))

/- Definition 60.5.2 (2): a homomorphism of divided power thickenings is a
divided-power map of the underlying rings over A whose induced quotient map
commutes with the two maps from C. -/
@[stacks 07HM] #check
  (DividedPowerThickening.Hom.{u, v, w} γ f X Y : Type w)

/- Definition 60.5.2 (3): CRIS(C/A, I, γ) is the category of divided power
thickenings of C over the fixed divided-power setup. -/
@[stacks 07HM] #check
  (DividedPowerThickening.CRIS.{u, v, w} γ f hIC h_pC :
    Type (max (max u v) (w + 1)))

/- Definition 60.5.2 (4): Cris(C/A, I, γ) is the full subcategory of
CRIS(C/A, I, γ) consisting of thickenings whose map C → B ⧸ J is an
isomorphism. -/
@[stacks 07HM] #check
  (DividedPowerThickening.Cris γ f hIC h_pC : Type (max u (v + 1)))
