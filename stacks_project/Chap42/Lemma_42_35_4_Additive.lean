/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Remark_42_33_5_Bivariant
public import ReasLib.AlgebraicGeometry.BivariantClass.Zero

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Pointwise addition of two bivariant classes. -/
def addClass
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
def negClass
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    BivariantClass delta f p where
  cap := fun {_ _} _ _ i f' g _ square k ↦ -c.cap i f' g square k
  map_proper := sorry
  pullback_flat := sorry
  gysin_cartier := sorry

/-- Repeated pointwise addition of a bivariant class. -/
def nsmulClass
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    ℕ → BivariantClass delta f p
  | 0 => zeroClass delta f p
  | n + 1 => addClass delta f p (nsmulClass delta f p c n) c

/-- Signed repeated pointwise addition of a bivariant class. -/
def zsmulClass
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    ℤ → BivariantClass delta f p
  | .ofNat n => nsmulClass delta f p c n
  | .negSucc n => negClass delta f p (nsmulClass delta f p c (n + 1))

/-- The pointwise-zero class has zero cap map. -/
theorem zeroClass_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left] (square : IsPullback i.left f'.left f.left g.left)
    (k : ℤ) : (zeroClass delta f p).cap i f' g square k = 0 := rfl

/-- Pointwise addition evaluates as addition of cap maps. -/
theorem addClass_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (c d : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ) :
    (addClass delta f p c d).cap i f' g square k =
      c.cap i f' g square k + d.cap i f' g square k := sorry

/-- Pointwise negation evaluates as negation of the cap map. -/
theorem negClass_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ) :
    (negClass delta f p c).cap i f' g square k = -c.cap i f' g square k := sorry

/-- Repeated addition starts with the pointwise-zero bivariant class. -/
theorem nsmulClass_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    nsmulClass delta f p c 0 = zeroClass delta f p := sorry

/-- Repeated addition at a successor adds one more copy. -/
theorem nsmulClass_succ
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) (n : ℕ) :
    nsmulClass delta f p c (n + 1) =
      addClass delta f p (nsmulClass delta f p c n) c := sorry

/-- Signed repeated addition agrees with natural repeated addition on nonnegative integers. -/
theorem zsmulClass_ofNat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) (n : ℕ) :
    zsmulClass delta f p c n = nsmulClass delta f p c n := sorry

/-- Bivariant classes form an additive commutative group under pointwise operations. -/
instance instAddCommGroup
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) : AddCommGroup (BivariantClass delta f p) where
  zero := zeroClass delta f p
  add := addClass delta f p
  neg := negClass delta f p
  sub := fun c d ↦ addClass delta f p c (negClass delta f p d)
  zero_add := sorry
  add_zero := sorry
  add_assoc := sorry
  add_comm := sorry
  neg_add_cancel := sorry
  sub_eq_add_neg := sorry
  nsmul := fun n c ↦ nsmulClass delta f p c n
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul := fun n c ↦ zsmulClass delta f p c n
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry

/-- The cap map of the zero bivariant class is zero. -/
theorem cap_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left] (square : IsPullback i.left f'.left f.left g.left)
    (k : ℤ) : (0 : BivariantClass delta f p).cap i f' g square k = 0 := sorry

/-- The cap map of a sum of bivariant classes is the pointwise sum. -/
theorem cap_add
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (c d : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ) :
    (c + d).cap i f' g square k = c.cap i f' g square k + d.cap i f' g square k := sorry

/-- The cap map of the negative of a bivariant class is the pointwise negative. -/
theorem cap_neg
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ) :
    (-c).cap i f' g square k = -c.cap i f' g square k := sorry

/-- The cap map of a difference of bivariant classes is the pointwise difference. -/
theorem cap_sub
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (c d : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ) :
    (c - d).cap i f' g square k = c.cap i f' g square k - d.cap i f' g square k := sorry

end AlgebraicGeometry.BivariantClass
