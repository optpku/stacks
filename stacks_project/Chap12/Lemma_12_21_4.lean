module

public import ReasLib.CategoryTheory.Homology.ExactCouple.PageFiltration
import StacksCheckRecall

/-!
# Lemma 12.21.4

Source-facing checks for the closed-form cycle and boundary filtration of the spectral sequence
associated to an exact couple.  The filtration recursion and page quotient are owned by the
generic spectral-sequence API; the exact-couple module supplies the kernel-image formulas and
representative calculation.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (X : ExactCouple C)
variable (K : Derived.Construction C)

/- Iteration of `α` uses the canonical monoid structure on `End X.A`; the standard `^` notation
is genuine exponentiation rather than a source-local notation. -/
#check (X.alphaPow 0 : End X.A)

/- Lemma 12.21.4 (1): the first boundary piece is zero, i.e. `B₁ = 0`. -/
@[stacks 011T]
#check (X.boundariesSubobject_zero :
  X.boundariesSubobject 0 = (⊥ : Subobject X.E))

/- Lemma 12.21.4 (2): the first cycle piece is all of `E`, i.e. `Z₁ = E`. -/
@[stacks 011T]
#check (X.cyclesSubobject_zero :
  X.cyclesSubobject 0 = (⊤ : Subobject X.E))

variable (r : ℕ)

#check (X.alphaPow r : End X.A)

/- Lemma 12.21.4 (3): the boundary piece on page `r + 1` is `g(Ker(α^r))`. -/
@[stacks 011T]
#check (Derived.Page.boundary_eq K X (Nat.succPNat r) :
  (K.associatedSpectralSequence X).boundary PUnit.unit (Nat.succPNat r) =
    X.boundariesSubobject r)

/- Lemma 12.21.4 (4): the cycle piece on page `r + 1` is `f⁻¹(Im(α^r))`. -/
@[stacks 011T]
#check (Derived.Page.cycle_eq K X (Nat.succPNat r) :
  (K.associatedSpectralSequence X).cycle PUnit.unit (Nat.succPNat r) =
    X.cyclesSubobject r)

section Monotonicity

variable {r s : ℕ} (hrs : r ≤ s)

/- Lemma 12.21.4 (5): the boundary pieces form an increasing filtration. -/
@[stacks 011T]
#check (X.boundariesSubobject_mono hrs :
  X.boundariesSubobject r ≤ X.boundariesSubobject s)

/- Lemma 12.21.4 (6): the cycle pieces form a decreasing filtration. -/
@[stacks 011T]
#check (X.cyclesSubobject_antitone hrs :
  X.cyclesSubobject s ≤ X.cyclesSubobject r)

end Monotonicity

/- Lemma 12.21.4 (7): every boundary piece lies in the corresponding cycle piece. -/
@[stacks 011T]
#check (X.boundariesSubobject_le_cyclesSubobject r :
  X.boundariesSubobject r ≤ X.cyclesSubobject r)

/- The literal formulas are compared to the canonical page object of the associated spectral
sequence, which is directly the middle object of the iterated exact couple. A quotient class
representative is explicit data, while `HomologyPageTower.Cycle.IsToPageOf` records its
compatibility with the generic map from cycles to that page. -/
@[stacks 011T "derived page comparison"]
#check (Derived.Page.objPositive K X r :
  (K.associatedSpectralSequence X).pageObject PUnit.unit (Nat.succPNat r) =
    (K.iterate X r).E)

variable (q : (X.cyclesSubobject r : C) ⟶ (K.iterate X r).E)
variable (hcycle : (K.associatedSpectralSequence X).cycle PUnit.unit (Nat.succPNat r) =
  X.cyclesSubobject r)
variable (hcycle' : (K.associatedSpectralSequence X).cycle PUnit.unit (Nat.succPNat r) =
  X.cyclesSubobject r)

#check (q : (X.cyclesSubobject r : C) ⟶ (K.iterate X r).E)
#check (HomologyPageTower.Cycle.toPageOf
  ((K.associatedSpectralSequence X).homologyPageTower PUnit.unit)
  (Nat.succPNat r)
  hcycle : (X.cyclesSubobject r : C) ⟶ (K.iterate X r).E)
#check (HomologyPageTower.Cycle.toPageOf_proof_irrel
  ((K.associatedSpectralSequence X).homologyPageTower PUnit.unit)
  (Nat.succPNat r)
  hcycle hcycle')
#check (HomologyPageTower.Cycle.IsToPageOf
  ((K.associatedSpectralSequence X).homologyPageTower PUnit.unit)
  (Nat.succPNat r)
  (X.cyclesSubobject r)
  q)
#check (HomologyPageTower.Cycle.toPageOf_isToPageOf
  ((K.associatedSpectralSequence X).homologyPageTower PUnit.unit)
  (Nat.succPNat r)
  hcycle)
#check @HomologyPageTower.Cycle.IsToPageOf.unique
#check ((K.iterate X r).d : (K.iterate X r).E ⟶ (K.iterate X r).E)

section Representatives

variable {T : C} (x : T ⟶ (X.cyclesSubobject r : C)) (y : T ⟶ X.A)
variable (hq : HomologyPageTower.Cycle.IsToPageOf
  ((K.associatedSpectralSequence X).homologyPageTower PUnit.unit)
  (Nat.succPNat r)
  (X.cyclesSubobject r)
  q)
variable (hfactor : (X.cyclesSubobject r).Factors (y ≫ X.g))
variable (hy : x ≫ (X.cyclesSubobject r).arrow ≫ X.f = y ≫ X.alphaPow r)

/- Lemma 12.21.4 (8): the induced page differential sends the class of `x` to the class
represented by `y ≫ g`. -/
@[stacks 011T]
#check (Derived.Page.differential_eq_on_representatives
  K X r q hq x y hfactor hy :
  x ≫ q ≫ (K.iterate X r).d = Derived.Page.boundaryClassMap K X r q y hfactor)

end Representatives

end ExactCouple
end CategoryTheory
