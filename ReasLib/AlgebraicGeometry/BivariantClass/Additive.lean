module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The bivariant class whose cap maps are pointwise zero. -/
def pointwiseZero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) : BivariantClass delta f p where
  cap := fun {_ _} _ _ _ _ _ _ _ _ ↦ 0
  map_proper := sorry
  pullback_flat := sorry
  gysin_cartier := sorry

/-- Pointwise addition of bivariant classes. -/
def pointwiseAdd
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c d : BivariantClass delta f p) :
    BivariantClass delta f p where
  cap := fun {_ _} _ _ i f' g _ square k ↦
    c.cap i f' g square k + d.cap i f' g square k
  map_proper := sorry
  pullback_flat := sorry
  gysin_cartier := sorry

/-- Pointwise negation of a bivariant class. -/
def pointwiseNeg
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    BivariantClass delta f p where
  cap := fun {_ _} _ _ i f' g _ square k ↦ -c.cap i f' g square k
  map_proper := sorry
  pullback_flat := sorry
  gysin_cartier := sorry

/-- Repeated pointwise addition of a bivariant class. -/
def pointwiseNsmul
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    ℕ → BivariantClass delta f p
  | 0 => pointwiseZero delta f p
  | n + 1 => pointwiseAdd delta f p (pointwiseNsmul delta f p c n) c

/-- Signed repeated pointwise addition of a bivariant class. -/
def pointwiseZsmul
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    ℤ → BivariantClass delta f p
  | .ofNat n => pointwiseNsmul delta f p c n
  | .negSucc n => pointwiseNeg delta f p (pointwiseNsmul delta f p c (n + 1))

/-- The explicit pointwise additive commutative group on bivariant classes. -/
@[reducible]
def pointwiseAddCommGroup
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) : AddCommGroup (BivariantClass delta f p) where
  zero := pointwiseZero delta f p
  add := pointwiseAdd delta f p
  neg := pointwiseNeg delta f p
  sub := fun c d ↦ pointwiseAdd delta f p c (pointwiseNeg delta f p d)
  zero_add := sorry
  add_zero := sorry
  add_assoc := sorry
  add_comm := sorry
  neg_add_cancel := sorry
  sub_eq_add_neg := sorry
  nsmul := fun n c ↦ pointwiseNsmul delta f p c n
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul := fun n c ↦ pointwiseZsmul delta f p c n
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry

/-- The cap map of the pointwise-zero bivariant class is zero. -/
theorem pointwiseZero_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left] (square : IsPullback i.left f'.left f.left g.left)
    (k : ℤ) : (pointwiseZero delta f p).cap i f' g square k = 0 := sorry

/-- The cap map of a pointwise sum is the sum of the cap maps. -/
theorem pointwiseAdd_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (c d : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ) :
    (pointwiseAdd delta f p c d).cap i f' g square k =
      c.cap i f' g square k + d.cap i f' g square k := sorry

/-- The cap map of a pointwise negative is the negative of the cap map. -/
theorem pointwiseNeg_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ) :
    (pointwiseNeg delta f p c).cap i f' g square k = -c.cap i f' g square k := sorry

end AlgebraicGeometry.BivariantClass
