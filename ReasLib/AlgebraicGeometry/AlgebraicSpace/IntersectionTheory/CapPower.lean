module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow

/-! # Powers of degree-one cap families -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowCohomology

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable {δ : Points B → ℤ} [IsDimensionFunction δ]
variable {f : X ⟶ B} [QuasiSeparated f] [LocallyOfFiniteType f]

/-- Zero-fold iteration is the identity cap family, reindexed along `k - 0 = k`. -/
def powCapZero : CapFamily δ f 0 :=
  fun {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    castChowGroup δ (g ≫ f) (sub_zero k).symm

/-- The successor stage composes a degree-one cap with a degree-`j` cap family. -/
def powCapSucc (c : CapFamily δ f 1) (j : ℕ)
    (ih : CapFamily δ f j) : CapFamily δ f (j + 1) :=
  fun {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    (castChowGroup δ (g ≫ f)
      (show (k - (j : ℤ)) - 1 = k - ((j + 1 : ℕ) : ℤ) by omega)).comp
      ((c g (k - (j : ℤ))).comp (ih g k))

/-- The natural-number powers of a degree-one additive cap family. -/
def powCap (c : CapFamily δ f 1) : (j : ℕ) → CapFamily δ f j :=
  Nat.rec powCapZero (fun j ih ↦ powCapSucc c j ih)

/-- The zeroth power is the identity with its degree reindexing. -/
theorem powCap_zero (c : CapFamily δ f 1) {Y : AlgebraicSpace S}
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    powCap c 0 g k = castChowGroup δ (g ≫ f) (sub_zero k).symm :=
  rfl

/-- The successor power applies the degree-one cap after the preceding power. -/
theorem powCap_succ (c : CapFamily δ f 1) (j : ℕ)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    powCap c (j + 1) g k =
      (castChowGroup δ (g ≫ f)
        (show (k - (j : ℤ)) - 1 = k - ((j + 1 : ℕ) : ℤ) by omega)).comp
        ((c g (k - (j : ℤ))).comp (powCap c j g k)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ChowCohomology
