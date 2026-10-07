module

public import ReasLib.Algebra.Module.IdealPower.Submodule

@[expose] public section

noncomputable section

universe u v

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The fixed-width ideal-power slice `I ^ q M / I ^ (q + n) M`, represented as
the quotient of the `q`th stage by its internal `n`th ideal-power stage. -/
abbrev PowerSlice (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (q n : ℕ) : Type v :=
  PowerSubmodule.stage I M q ⧸
    PowerSubmodule.stage I (PowerSubmodule.stage I M q) n

namespace PowerSlice

variable (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- The internal denominator of a fixed-width slice is the comap of the ambient
`(q + n)`th ideal-power stage. -/
theorem denominator_eq_comap (q n : ℕ) :
    PowerSubmodule.stage I (PowerSubmodule.stage I M q) n =
      (PowerSubmodule.stage I M (q + n)).comap
        (PowerSubmodule.subtype I M q) := sorry

/-- The quotient map from the numerator stage to a fixed-width ideal-power slice. -/
def mk (q n : ℕ) :
    PowerSubmodule.stage I M q →ₗ[A] PowerSlice I M q n :=
  Submodule.mkQ (PowerSubmodule.stage I (PowerSubmodule.stage I M q) n)

/-- The slice quotient map sends a stage representative to its quotient class. -/
theorem mk_apply (q n : ℕ) (x : PowerSubmodule.stage I M q) :
    mk I M q n x = (Submodule.Quotient.mk x : PowerSlice I M q n) := sorry

/-- Inclusion from a deeper numerator stage carries the fixed-width denominator
into the corresponding denominator at a shallower stage. -/
theorem transition_mapsTo (n q r : ℕ) (h : r ≤ q) :
    PowerSubmodule.stage I (PowerSubmodule.stage I M q) n ≤
      (PowerSubmodule.stage I (PowerSubmodule.stage I M r) n).comap
        (Submodule.inclusion (PowerSubmodule.stage_antitone I h)) := sorry

/-- The canonical transition from the slice beginning at `q` to the slice beginning at `r`. -/
def transition (n q r : ℕ) (h : r ≤ q) :
    PowerSlice I M q n →ₗ[A] PowerSlice I M r n :=
  Submodule.mapQ
    (PowerSubmodule.stage I (PowerSubmodule.stage I M q) n)
    (PowerSubmodule.stage I (PowerSubmodule.stage I M r) n)
    (Submodule.inclusion (PowerSubmodule.stage_antitone I h)) (transition_mapsTo I M n q r h)

/-- A slice transition sends a quotient representative to the same ambient element
viewed in the shallower numerator stage. -/
theorem transition_mk (n q r : ℕ) (h : r ≤ q)
    (x : PowerSubmodule.stage I M q) :
    transition I M n q r h (mk I M q n x) =
      mk I M r n (Submodule.inclusion (PowerSubmodule.stage_antitone I h) x) := sorry

/-- Multiplication by a coefficient in `I ^ c` sends the `q`th ideal-power stage
into every stage of exponent at most `q + c`. -/
theorem coefficient_smul_mem (q r c : ℕ) (a : (I ^ c : Ideal A)) (h : r ≤ q + c)
    (x : M) (hx : x ∈ PowerSubmodule.stage I M q) :
    (a : A) • x ∈ PowerSubmodule.stage I M r := sorry

/-- Multiplication by a coefficient, restricted between the indicated numerator stages. -/
def smulStageTo (q r c : ℕ) (a : (I ^ c : Ideal A)) (h : r ≤ q + c) :
    PowerSubmodule.stage I M q →ₗ[A] PowerSubmodule.stage I M r :=
  (LinearMap.lsmul A M (a : A)).restrict
    (coefficient_smul_mem I M q r c a h)

/-- The restricted coefficient map evaluates as ambient scalar multiplication. -/
theorem smulStageTo_apply (q r c : ℕ) (a : (I ^ c : Ideal A)) (h : r ≤ q + c)
    (x : PowerSubmodule.stage I M q) :
    (smulStageTo I M q r c a h x : M) = (a : A) • (x : M) := sorry

/-- Coefficient multiplication carries the source slice denominator into the
target slice denominator. -/
theorem smulTo_mapsTo (n q r c : ℕ) (a : (I ^ c : Ideal A)) (h : r ≤ q + c) :
    PowerSubmodule.stage I (PowerSubmodule.stage I M q) n ≤
      (PowerSubmodule.stage I (PowerSubmodule.stage I M r) n).comap
        (smulStageTo I M q r c a h) := sorry

/-- Multiplication by a coefficient in `I ^ c` from the slice at `q` to the slice at `r`. -/
def smulTo (n q r c : ℕ) (a : (I ^ c : Ideal A)) (h : r ≤ q + c) :
    PowerSlice I M q n →ₗ[A] PowerSlice I M r n :=
  Submodule.mapQ
    (PowerSubmodule.stage I (PowerSubmodule.stage I M q) n)
    (PowerSubmodule.stage I (PowerSubmodule.stage I M r) n)
    (smulStageTo I M q r c a h) (smulTo_mapsTo I M n q r c a h)

/-- Coefficient multiplication on a slice sends a representative to the class
of its scalar multiple. -/
theorem smulTo_mk (n q r c : ℕ) (a : (I ^ c : Ideal A)) (h : r ≤ q + c)
    (x : PowerSubmodule.stage I M q) :
    smulTo I M n q r c a h (mk I M q n x) =
      mk I M r n (smulStageTo I M q r c a h x) := sorry

/-- The coefficient shift from exponent `n - (2 + d) * c` reaches the slice at
exponent `n - (1 + d) * c`. -/
theorem coefficientIndex_le (n c d : ℕ) :
    n - (1 + d) * c ≤ n - (2 + d) * c + c := sorry

end PowerSlice

end Ideal
