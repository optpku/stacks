module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct

/-!
# Three-by-three coherence for finite-length determinant lines

An exact three-by-three diagram determines row-first and signed column-first maps between
determinant lines. The interchange of the upper-right and lower-left factors carries the
Koszul sign determined by their lengths.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- An exact three-by-three diagram of finite-length modules over a local ring. -/
structure ThreeByThree (R : Type u) [CommRing R] [IsLocalRing R] where
  /-- The top short complex `A ⟶ B ⟶ C`. -/
  top : ShortComplex (ModuleCat.{v} R)
  /-- The middle short complex `D ⟶ E ⟶ F`. -/
  middle : ShortComplex (ModuleCat.{v} R)
  /-- The bottom short complex `G ⟶ H ⟶ I`. -/
  bottom : ShortComplex (ModuleCat.{v} R)
  /-- The morphism from the top row to the middle row. -/
  upper : top ⟶ middle
  /-- The morphism from the middle row to the bottom row. -/
  lower : middle ⟶ bottom
  /-- The left pair of vertical maps has zero composite. -/
  zeroLeft : upper.τ₁ ≫ lower.τ₁ = 0
  /-- The middle pair of vertical maps has zero composite. -/
  zeroMiddle : upper.τ₂ ≫ lower.τ₂ = 0
  /-- The right pair of vertical maps has zero composite. -/
  zeroRight : upper.τ₃ ≫ lower.τ₃ = 0
  /-- The upper-left module has finite length. -/
  topFiniteLeft : IsFiniteLength R top.X₁
  /-- The upper-middle module has finite length. -/
  topFiniteMiddle : IsFiniteLength R top.X₂
  /-- The upper-right module has finite length. -/
  topFiniteRight : IsFiniteLength R top.X₃
  /-- The center-left module has finite length. -/
  middleFiniteLeft : IsFiniteLength R middle.X₁
  /-- The center module has finite length. -/
  middleFiniteMiddle : IsFiniteLength R middle.X₂
  /-- The center-right module has finite length. -/
  middleFiniteRight : IsFiniteLength R middle.X₃
  /-- The lower-left module has finite length. -/
  bottomFiniteLeft : IsFiniteLength R bottom.X₁
  /-- The lower-middle module has finite length. -/
  bottomFiniteMiddle : IsFiniteLength R bottom.X₂
  /-- The lower-right module has finite length. -/
  bottomFiniteRight : IsFiniteLength R bottom.X₃
  /-- The top row is short exact. -/
  topExact : top.ShortExact
  /-- The middle row is short exact. -/
  middleExact : middle.ShortExact
  /-- The bottom row is short exact. -/
  bottomExact : bottom.ShortExact
  /-- The left column is short exact. -/
  leftExact : (ShortComplex.mk upper.τ₁ lower.τ₁ zeroLeft).ShortExact
  /-- The middle column is short exact. -/
  centerExact : (ShortComplex.mk upper.τ₂ lower.τ₂ zeroMiddle).ShortExact
  /-- The right column is short exact. -/
  rightExact : (ShortComplex.mk upper.τ₃ lower.τ₃ zeroRight).ShortExact

namespace ThreeByThree

/-- Construct an exact three-by-three diagram from its rows, vertical maps, finite-length
hypotheses, and row and column exactness proofs. -/
def ofRows (top middle bottom : ShortComplex (ModuleCat.{v} R))
    (upper : top ⟶ middle) (lower : middle ⟶ bottom)
    (zeroLeft : upper.τ₁ ≫ lower.τ₁ = 0)
    (zeroMiddle : upper.τ₂ ≫ lower.τ₂ = 0)
    (zeroRight : upper.τ₃ ≫ lower.τ₃ = 0)
    (topFiniteLeft : IsFiniteLength R top.X₁)
    (topFiniteMiddle : IsFiniteLength R top.X₂)
    (topFiniteRight : IsFiniteLength R top.X₃)
    (middleFiniteLeft : IsFiniteLength R middle.X₁)
    (middleFiniteMiddle : IsFiniteLength R middle.X₂)
    (middleFiniteRight : IsFiniteLength R middle.X₃)
    (bottomFiniteLeft : IsFiniteLength R bottom.X₁)
    (bottomFiniteMiddle : IsFiniteLength R bottom.X₂)
    (bottomFiniteRight : IsFiniteLength R bottom.X₃)
    (topExact : top.ShortExact) (middleExact : middle.ShortExact)
    (bottomExact : bottom.ShortExact)
    (leftExact : (ShortComplex.mk upper.τ₁ lower.τ₁ zeroLeft).ShortExact)
    (centerExact : (ShortComplex.mk upper.τ₂ lower.τ₂ zeroMiddle).ShortExact)
    (rightExact : (ShortComplex.mk upper.τ₃ lower.τ₃ zeroRight).ShortExact) :
    ThreeByThree R :=
  { top, middle, bottom, upper, lower, zeroLeft, zeroMiddle, zeroRight,
    topFiniteLeft, topFiniteMiddle, topFiniteRight,
    middleFiniteLeft, middleFiniteMiddle, middleFiniteRight,
    bottomFiniteLeft, bottomFiniteMiddle, bottomFiniteRight,
    topExact, middleExact, bottomExact, leftExact, centerExact, rightExact }

/-- The left column `A ⟶ D ⟶ G` of an exact three-by-three diagram. -/
def columnLeft (D : ThreeByThree.{u, v} R) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk D.upper.τ₁ D.lower.τ₁ D.zeroLeft

/-- The middle column `B ⟶ E ⟶ H` of an exact three-by-three diagram. -/
def columnMiddle (D : ThreeByThree.{u, v} R) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk D.upper.τ₂ D.lower.τ₂ D.zeroMiddle

/-- The right column `C ⟶ F ⟶ I` of an exact three-by-three diagram. -/
def columnRight (D : ThreeByThree.{u, v} R) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk D.upper.τ₃ D.lower.τ₃ D.zeroRight

/-- The row-first determinant route through the top and bottom rows and then the middle
column. -/
def viaRows (D : ThreeByThree.{u, v} R) :
    ((Module.FiniteLengthDeterminant R D.top.X₁ D.topFiniteLeft ⊗[IsLocalRing.ResidueField R]
          Module.FiniteLengthDeterminant R D.top.X₃ D.topFiniteRight) ⊗[IsLocalRing.ResidueField R]
        (Module.FiniteLengthDeterminant R D.bottom.X₁ D.bottomFiniteLeft ⊗[IsLocalRing.ResidueField R]
          Module.FiniteLengthDeterminant R D.bottom.X₃ D.bottomFiniteRight))
      →ₗ[IsLocalRing.ResidueField R]
        Module.FiniteLengthDeterminant R D.middle.X₂ D.middleFiniteMiddle :=
  (exactEquiv (columnMiddle D) D.topFiniteMiddle D.middleFiniteMiddle
      D.bottomFiniteMiddle D.centerExact).toLinearMap.comp
    (TensorProduct.congr
      (exactEquiv D.top D.topFiniteLeft D.topFiniteMiddle D.topFiniteRight D.topExact)
      (exactEquiv D.bottom D.bottomFiniteLeft D.bottomFiniteMiddle
        D.bottomFiniteRight D.bottomExact)).toLinearMap

/-- The column-first determinant route, including the signed interchange of the `C` and `G`
factors. -/
def viaColumns (D : ThreeByThree.{u, v} R) :
    ((Module.FiniteLengthDeterminant R D.top.X₁ D.topFiniteLeft ⊗[IsLocalRing.ResidueField R]
          Module.FiniteLengthDeterminant R D.top.X₃ D.topFiniteRight) ⊗[IsLocalRing.ResidueField R]
        (Module.FiniteLengthDeterminant R D.bottom.X₁ D.bottomFiniteLeft ⊗[IsLocalRing.ResidueField R]
          Module.FiniteLengthDeterminant R D.bottom.X₃ D.bottomFiniteRight))
      →ₗ[IsLocalRing.ResidueField R]
        Module.FiniteLengthDeterminant R D.middle.X₂ D.middleFiniteMiddle :=
  (exactEquiv D.middle D.middleFiniteLeft D.middleFiniteMiddle
      D.middleFiniteRight D.middleExact).toLinearMap.comp
    ((TensorProduct.congr
      (exactEquiv (columnLeft D) D.topFiniteLeft D.middleFiniteLeft
        D.bottomFiniteLeft D.leftExact)
      (exactEquiv (columnRight D) D.topFiniteRight D.middleFiniteRight
        D.bottomFiniteRight D.rightExact)).toLinearMap.comp
      (ModuleCat.TensorProduct.koszulShuffle (IsLocalRing.ResidueField R)
        (ModuleCat.of (IsLocalRing.ResidueField R)
          (Module.FiniteLengthDeterminant R D.top.X₁ D.topFiniteLeft))
        (ModuleCat.of (IsLocalRing.ResidueField R)
          (Module.FiniteLengthDeterminant R D.top.X₃ D.topFiniteRight))
        (ModuleCat.of (IsLocalRing.ResidueField R)
          (Module.FiniteLengthDeterminant R D.bottom.X₁ D.bottomFiniteLeft))
        (ModuleCat.of (IsLocalRing.ResidueField R)
          (Module.FiniteLengthDeterminant R D.bottom.X₃ D.bottomFiniteRight))
        (length R D.top.X₃ D.topFiniteRight : ℤ)
        (length R D.bottom.X₁ D.bottomFiniteLeft : ℤ)).hom)

/-- The row-first and signed column-first determinant routes in an exact three-by-three diagram
agree. -/
theorem commutes (D : ThreeByThree.{u, v} R) : viaRows D = viaColumns D := sorry

end ThreeByThree

end Module.FiniteLengthDeterminant
