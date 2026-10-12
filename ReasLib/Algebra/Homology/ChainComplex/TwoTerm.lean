/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Double
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-term chain complexes

This file specializes `HomologicalComplex.double` to chain complexes in consecutive natural
degrees.  A morphism `f : X ⟶ Y` is placed in degrees `k + 1` and `k`, and all functorial,
endpoint, splitting, and exactness APIs are inherited from the generic construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

universe v u

namespace ChainComplex

namespace twoTerm

/-- The chain-complex relation from degree `k + 1` to degree `k`. -/
@[stacks 0192 "relation for a two-term chain complex"]
abbrev rel (k : ℕ) : (ComplexShape.down ℕ).Rel (k + 1) k :=
  ComplexShape.down_mk (k + 1) k rfl

end twoTerm

section Basic

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The chain complex with differential `f : X ⟶ Y` from degree `k + 1` to degree `k`. -/
@[stacks 0192 "two-term chain complex"]
noncomputable abbrev twoTerm {X Y : C} (f : X ⟶ Y) (k : ℕ) :
    ChainComplex C ℕ :=
  HomologicalComplex.double f (twoTerm.rel k)

namespace twoTerm

/-- The canonical identification of the upper term of a two-term complex with its source. -/
@[stacks 0192 "upper term of a two-term chain complex"]
noncomputable abbrev upperIso {X Y : C} (f : X ⟶ Y) (k : ℕ) :
    (twoTerm f k).X (k + 1) ≅ X :=
  HomologicalComplex.doubleXIso₀ f (rel k)

/-- The canonical identification of the lower term of a two-term complex with its target. -/
@[stacks 0192 "lower term of a two-term chain complex"]
noncomputable abbrev lowerIso {X Y : C} (f : X ⟶ Y) (k : ℕ) :
    (twoTerm f k).X k ≅ Y :=
  HomologicalComplex.doubleXIso₁ f (rel k) (Nat.succ_ne_self k)

/-- The differential of a two-term complex is its defining morphism under the endpoint
identifications. -/
@[simp, stacks 0192 "differential of a two-term chain complex"]
theorem d {X Y : C} (f : X ⟶ Y) (k : ℕ) :
    (twoTerm f k).d (k + 1) k =
      (upperIso f k).hom ≫ f ≫ (lowerIso f k).inv := sorry

/-- Every term outside degrees `k + 1` and `k` in a two-term complex is zero. -/
@[stacks 0192 "vanishing outside a two-term chain complex"]
theorem isZero_X {X Y : C} (f : X ⟶ Y) (k n : ℕ)
    (hUpper : n ≠ k + 1) (hLower : n ≠ k) :
    IsZero ((twoTerm f k).X n) := sorry

/-- A commutative square induces a map of two-term chain complexes. -/
@[stacks 0192 "map of two-term chain complexes"]
noncomputable abbrev map {f g : Arrow C} (φ : f ⟶ g) (k : ℕ) :
    twoTerm f.hom k ⟶ twoTerm g.hom k :=
  HomologicalComplex.double.map (rel k) (Nat.succ_ne_self k) φ

namespace map

/-- The upper component of a map of two-term complexes is the left side of its defining
square. -/
@[simp, stacks 0192 "upper component of a map of two-term chain complexes"]
theorem upper {f g : Arrow C} (φ : f ⟶ g) (k : ℕ) :
    (map φ k).f (k + 1) =
      (upperIso f.hom k).hom ≫ φ.left ≫ (upperIso g.hom k).inv := sorry

/-- The lower component of a map of two-term complexes is the right side of its defining
square. -/
@[simp, stacks 0192 "lower component of a map of two-term chain complexes"]
theorem lower {f g : Arrow C} (φ : f ⟶ g) (k : ℕ) :
    (map φ k).f k =
      (lowerIso f.hom k).hom ≫ φ.right ≫ (lowerIso g.hom k).inv := sorry

end map

/-- Two-term chain complexes in degrees `k + 1` and `k` form a functor on the arrow
category. -/
@[stacks 0192 "two-term chain complex functor"]
noncomputable abbrev functor (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] (k : ℕ) : Arrow C ⥤ ChainComplex C ℕ :=
  HomologicalComplex.double.functor C (rel k) (Nat.succ_ne_self k)

/-- The two-term functor sends an arrow to its associated two-term chain complex. -/
@[simp, stacks 0192 "two-term chain complex functor object formula"]
theorem functor_obj (f : Arrow C) (k : ℕ) :
    (functor C k).obj f = twoTerm f.hom k := sorry

/-- The two-term functor sends a square to the corresponding map of two-term complexes. -/
@[simp, stacks 0192 "two-term chain complex functor map formula"]
theorem functor_map {f g : Arrow C} (φ : f ⟶ g) (k : ℕ) :
    (functor C k).map φ = map φ k := sorry

/-- The canonical inclusion of the lower endpoint single complex into a two-term complex. -/
@[stacks 0192 "lower endpoint inclusion into a two-term chain complex"]
noncomputable abbrev ιApp (f : Arrow C) (k : ℕ) :
    (single C (ComplexShape.down ℕ) k).obj f.right ⟶ twoTerm f.hom k :=
  HomologicalComplex.double.ιApp f (rel k) (Nat.succ_ne_self k)

/-- The lower endpoint inclusions form a natural transformation into the two-term functor. -/
@[stacks 0192 "natural lower endpoint inclusion into two-term chain complexes"]
noncomputable abbrev ι (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] (k : ℕ) :
    (Arrow.rightFunc : Arrow C ⥤ C) ⋙ single C (ComplexShape.down ℕ) k ⟶
      functor C k :=
  HomologicalComplex.double.ι C (rel k) (Nat.succ_ne_self k)

/-- The component of the natural lower endpoint inclusion is `ιApp`. -/
@[simp, stacks 0192 "lower endpoint inclusion component formula"]
theorem ι_app (f : Arrow C) (k : ℕ) :
    (ι C k).app f = ιApp f k := sorry

/-- The canonical projection from a two-term complex onto the upper endpoint single complex. -/
@[stacks 0192 "upper endpoint projection from a two-term chain complex"]
noncomputable abbrev πApp (f : Arrow C) (k : ℕ) :
    twoTerm f.hom k ⟶
      (single C (ComplexShape.down ℕ) (k + 1)).obj f.left :=
  HomologicalComplex.double.πApp f (rel k)

/-- The upper endpoint projections form a natural transformation out of the two-term
functor. -/
@[stacks 0192 "natural upper endpoint projection from two-term chain complexes"]
noncomputable abbrev π (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] (k : ℕ) :
    functor C k ⟶
      (Arrow.leftFunc : Arrow C ⥤ C) ⋙ single C (ComplexShape.down ℕ) (k + 1) :=
  HomologicalComplex.double.π C (rel k) (Nat.succ_ne_self k)

/-- The component of the natural upper endpoint projection is `πApp`. -/
@[simp, stacks 0192 "upper endpoint projection component formula"]
theorem π_app (f : Arrow C) (k : ℕ) :
    (π C k).app f = πApp f k := sorry

/-- The natural lower inclusion and upper projection compose to zero. -/
@[stacks 0192 "single-two-term-single composition"]
theorem ι_comp_π (k : ℕ) :
    ι C k ≫ π C k = 0 := sorry

/-- The canonical lower-single--two-term--upper-single short complex, functorial in the
underlying arrow. -/
@[stacks 0192 "functorial single-two-term-single short complex"]
noncomputable abbrev shortComplex (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] [HasZeroObject C] (k : ℕ) :
    ShortComplex (Arrow C ⥤ ChainComplex C ℕ) :=
  HomologicalComplex.double.shortComplex C (rel k) (Nat.succ_ne_self k)

namespace shortComplex

/-- Evaluate the functorial single--two-term--single row at an arrow. -/
@[stacks 0192 "single-two-term-single short complex at an arrow"]
abbrev app (f : Arrow C) (k : ℕ) : ShortComplex (ChainComplex C ℕ) :=
  HomologicalComplex.double.shortComplex.app (C := C)
    (rel k) (Nat.succ_ne_self k) f

end shortComplex

end twoTerm

end Basic

namespace twoTerm

section Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace degree

/-- The degreewise retraction from a two-term complex onto its lower endpoint single
complex. -/
@[stacks 0192 "degreewise retraction of a two-term chain complex"]
noncomputable abbrev retraction (f : Arrow C) (k n : ℕ) :
    (twoTerm f.hom k).X n ⟶
      ((single C (ComplexShape.down ℕ) k).obj f.right).X n :=
  HomologicalComplex.double.degree.retraction
    f (rel k) (Nat.succ_ne_self k) n

/-- The degreewise section of the upper endpoint single quotient into a two-term complex. -/
@[stacks 0192 "degreewise section of a two-term chain complex"]
noncomputable abbrev section_ (f : Arrow C) (k n : ℕ) :
    ((single C (ComplexShape.down ℕ) (k + 1)).obj f.left).X n ⟶
      (twoTerm f.hom k).X n :=
  HomologicalComplex.double.degree.section_ f (rel k) n

/-- The explicit splitting of the single--two-term--single row in chain degree `n`. -/
@[stacks 0192 "degreewise splitting of a two-term chain complex"]
noncomputable abbrev splitting (f : Arrow C) (k n : ℕ) :
    ((shortComplex.app f k).degreewise n).Splitting :=
  HomologicalComplex.double.degree.splitting
    f (rel k) (Nat.succ_ne_self k) n

end degree

/-- The chosen family of degreewise splittings of the single--two-term--single row. -/
@[stacks 0192 "chosen degreewise splitting of a two-term chain complex"]
noncomputable abbrev degreewiseSplitting (f : Arrow C) (k : ℕ) :
    ShortComplex.DegreewiseSplitting (shortComplex.app f k) :=
  HomologicalComplex.double.degreewiseSplitting
    f (rel k) (Nat.succ_ne_self k)

/-- The single--two-term--single row associated to an arrow is degreewise split. -/
@[stacks 0192 "degreewise-split two-term chain complex row"]
theorem isDegreewiseSplit (f : Arrow C) (k : ℕ) :
    (shortComplex.app f k).IsDegreewiseSplit := sorry

/-- A two-term chain complex whose differential is an isomorphism is acyclic. -/
@[stacks 0192 "acyclic two-term chain complex with invertible differential"]
theorem acyclic_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] (k : ℕ) :
    (twoTerm f k).Acyclic := sorry

end Splitting

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical single--two-term--single row is short exact in an abelian category. -/
@[stacks 0192 "short exact single-two-term-single row"]
theorem shortComplex.app.shortExact (f : Arrow C) (k : ℕ) :
    (shortComplex.app f k).ShortExact := sorry

end Abelian

end twoTerm

end ChainComplex
