module

public import ReasLib.CategoryTheory.Triangulated.TStructure.Functor.Bounds
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomological Amplitude of Functors

This file combines the independent lower and upper t-structure bounds into an interval-valued
cohomological amplitude.  The one-sided API remains available from the narrower `Bounds` leaf.
-/

open CategoryTheory
open CategoryTheory.Limits

universe uC vC uD vD uE vE

namespace CategoryTheory.Functor.TStructure

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 07K7 and 07K8: a functor has cohomological amplitude `[p, q]` when it maps lower
bounds by `p` and upper bounds by `q`. -/
@[stacks 07K7, stacks 07K8]
def HasAmplitude (F : C ⥤ D) (tC : Triangulated.TStructure C)
    (tD : Triangulated.TStructure D) (p q : ℤ) : Prop :=
  MapsGE F tC tD p ∧ MapsLE F tC tD q

namespace HasAmplitude

variable {F G : C ⥤ D}
variable {tC : Triangulated.TStructure C} {tD : Triangulated.TStructure D}
variable {p q : ℤ}

/-- The lower-bound component of a cohomological-amplitude statement. -/
theorem mapsGE (h : HasAmplitude F tC tD p q) : MapsGE F tC tD p := sorry

/-- The upper-bound component of a cohomological-amplitude statement. -/
theorem mapsLE (h : HasAmplitude F tC tD p q) : MapsLE F tC tD q := sorry

/-- Apply both amplitude bounds to one object with specified source bounds. -/
theorem obj (h : HasAmplitude F tC tD p q) (X : C) (a b : ℤ)
    (hGE : tC.IsGE X a) (hLE : tC.IsLE X b) :
    tD.IsGE (F.obj X) (a + p) ∧ tD.IsLE (F.obj X) (b + q) := sorry

/-- Cohomological amplitude is invariant under a natural isomorphism of functors. -/
theorem ofIso (h : HasAmplitude F tC tD p q) (e : F ≅ G) :
    HasAmplitude G tC tD p q := sorry

/-- An amplitude interval may be enlarged on either side. -/
theorem mono {p' q' : ℤ} (h : HasAmplitude F tC tD p q)
    (hp : p' ≤ p) (hq : q ≤ q') : HasAmplitude F tC tD p' q' := sorry

/-- The identity functor has cohomological amplitude `[0, 0]`. -/
theorem id : HasAmplitude (𝟭 C) tC tC 0 0 := sorry

variable {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
variable {H : D ⥤ E} {tE : Triangulated.TStructure E} {r s : ℤ}

/-- Amplitudes add under composition of functors. -/
theorem comp (hF : HasAmplitude F tC tD p q) (hH : HasAmplitude H tD tE r s) :
    HasAmplitude (F ⋙ H) tC tE (p + r) (q + s) := sorry

end HasAmplitude

end CategoryTheory.Functor.TStructure
