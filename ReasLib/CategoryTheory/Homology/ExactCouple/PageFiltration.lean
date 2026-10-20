/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.ExactCouple.Derived
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration

/-!
# Page Filtrations from Exact Couples

The classical kernel-image filtration is compared with a spectral sequence assembled from an
explicit `Derived.Construction`. Concrete quotient maps accept the comparison evidence they use;
the comparison theorems themselves remain proposition-valued.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical monoid power of an exact-couple outer endomorphism. -/
@[stacks 011T]
abbrev alphaPow (X : ExactCouple C) (r : ℕ) : End X.A :=
  (End.of X.α) ^ r

/-- The zeroth power of the outer endomorphism is the identity. -/
@[simp]
theorem alphaPow_zero (X : ExactCouple C) : X.alphaPow 0 = 𝟙 X.A := sorry

/-- A successor power appends one copy of the outer endomorphism on the right. -/
theorem alphaPow_succ (X : ExactCouple C) (r : ℕ) :
    X.alphaPow (r + 1) = X.alphaPow r ≫ X.α := sorry

/-- Powers of the outer endomorphism compose by addition. -/
theorem alphaPow_add (X : ExactCouple C) (r s : ℕ) :
    X.alphaPow (r + s) = X.alphaPow r ≫ X.alphaPow s := sorry

namespace AlphaPow

/-- An exact-couple morphism commutes with every power of the outer endomorphism. -/
@[stacks 011T "naturality of outer endomorphism powers"]
theorem naturality {X Y : ExactCouple C} (φ : Hom X Y) (r : ℕ) :
    X.alphaPow r ≫ φ.a = φ.a ≫ Y.alphaPow r := sorry

end AlphaPow

/-- The closed-form cycle piece `f⁻¹(Im(α^r))` inside the initial page object. -/
@[stacks 011T]
abbrev cyclesSubobject (X : ExactCouple C) (r : ℕ) : Subobject X.E :=
  (Subobject.pullback X.f).obj (imageSubobject (X.alphaPow r))

/-- The closed-form boundary piece `g(Ker(α^r))` inside the initial page object. -/
@[stacks 011T]
abbrev boundariesSubobject (X : ExactCouple C) (r : ℕ) : Subobject X.E :=
  imageSubobject ((kernelSubobject (X.alphaPow r)).arrow ≫ X.g)

/-- The first closed-form boundary piece is zero. -/
@[stacks 011T]
theorem boundariesSubobject_zero (X : ExactCouple C) :
    X.boundariesSubobject 0 = (⊥ : Subobject X.E) := sorry

/-- The first closed-form cycle piece is the whole initial page object. -/
@[stacks 011T]
theorem cyclesSubobject_zero (X : ExactCouple C) :
    X.cyclesSubobject 0 = (⊤ : Subobject X.E) := sorry

/-- The boundary pieces form an increasing filtration. -/
@[stacks 011T]
theorem boundariesSubobject_mono (X : ExactCouple C) {r s : ℕ} (hrs : r ≤ s) :
    X.boundariesSubobject r ≤ X.boundariesSubobject s := sorry

/-- The cycle pieces form a decreasing filtration. -/
@[stacks 011T]
theorem cyclesSubobject_antitone (X : ExactCouple C) {r s : ℕ} (hrs : r ≤ s) :
    X.cyclesSubobject s ≤ X.cyclesSubobject r := sorry

/-- Every closed-form boundary piece lies in the corresponding cycle piece. -/
@[stacks 011T]
theorem boundariesSubobject_le_cyclesSubobject (X : ExactCouple C) (r : ℕ) :
    X.boundariesSubobject r ≤ X.cyclesSubobject r := sorry

namespace Derived.Page

/-- The associated boundary filtration is the closed-form image of `Ker(α^r)`. -/
@[stacks 011T]
theorem boundary_eq
    (K : Derived.Construction C) (X : ExactCouple C) (r : ℕ+) :
    (K.associatedSpectralSequence X).boundary PUnit.unit r =
      X.boundariesSubobject r.natPred := sorry

/-- The associated cycle filtration is the closed-form inverse image of `Im(α^r)`. -/
@[stacks 011T]
theorem cycle_eq
    (K : Derived.Construction C) (X : ExactCouple C) (r : ℕ+) :
    (K.associatedSpectralSequence X).cycle PUnit.unit r =
      X.cyclesSubobject r.natPred := sorry

/-- The positive page at index `r + 1` is the middle object of the `r`-fold iterate. -/
@[stacks 011S "derived page comparison"]
theorem objPositive
    (K : Derived.Construction C) (X : ExactCouple C) (r : ℕ) :
    (K.associatedSpectralSequence X).pageObject PUnit.unit (Nat.succPNat r) =
      (K.iterate X r).E := sorry

/-- The quotient class represented by `y ≫ g`, using an explicit class map and factorization. -/
@[stacks 011T]
noncomputable def boundaryClassMap
    (K : Derived.Construction C) (X : ExactCouple C) {T : C} (r : ℕ)
    (q : (X.cyclesSubobject r : C) ⟶ (K.iterate X r).E)
    (y : T ⟶ X.A) (hfactor : (X.cyclesSubobject r).Factors (y ≫ X.g)) :
    T ⟶ (K.iterate X r).E :=
  (X.cyclesSubobject r).factorThru (y ≫ X.g) hfactor ≫ q

/- The representative formula is stated directly on the iterated page object, avoiding a
definitionally identical quotient wrapper. -/
/-- On a representative satisfying `x ≫ f = y ≫ α^r`, the page differential sends its class
to the class represented by `y ≫ g`. -/
@[stacks 011T]
theorem differential_eq_on_representatives
    (K : Derived.Construction C) (X : ExactCouple C) {T : C} (r : ℕ)
    (q : (X.cyclesSubobject r : C) ⟶ (K.iterate X r).E)
    (hq : HomologyPageTower.Cycle.IsToPageOf
      ((K.associatedSpectralSequence X).homologyPageTower PUnit.unit)
      (Nat.succPNat r)
      (X.cyclesSubobject r)
      q)
    (x : T ⟶ (X.cyclesSubobject r : C)) (y : T ⟶ X.A)
    (hfactor : (X.cyclesSubobject r).Factors (y ≫ X.g))
    (hy : x ≫ (X.cyclesSubobject r).arrow ≫ X.f = y ≫ X.alphaPow r) :
    x ≫ q ≫ (K.iterate X r).d = boundaryClassMap K X r q y hfactor := sorry

end Derived.Page

end ExactCouple
end CategoryTheory
