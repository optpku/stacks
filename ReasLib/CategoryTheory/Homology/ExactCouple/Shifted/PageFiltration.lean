/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.ExactCouple.Shifted
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural

/-!
# Closed-Form Filtrations for Shifted Exact Couples

This module expresses the cycle and boundary filtrations of the associated shifted spectral
sequence using the iterated translated outer maps of a shifted exact couple.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ShiftedExactCouple

section Basic

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {S T : C ≌ C}

/-- The source of the `r`-fold forward translated outer map, expressed through the shared
zero-based endofunctor iterate. -/
@[stacks 0AMJ "forward translated outer-map source"]
abbrev tAlphaSource (X : ShiftedExactCouple S T) (r : ℕ) : C :=
  (Endofunctor.iterate T.functor r).obj X.A

namespace TAlphaSource

/-- The source of the zeroth forward translated outer map is `A`. -/
@[simp]
theorem zero (X : ShiftedExactCouple S T) :
    X.tAlphaSource 0 = X.A := sorry

/-- The source of the successor forward translated outer map is one further `T`-translate. -/
@[simp]
theorem succ (X : ShiftedExactCouple S T) (r : ℕ) :
    X.tAlphaSource (r + 1) = T.functor.obj (X.tAlphaSource r) := sorry

/-- The recursively bracketed source is the object obtained from the canonical power `T ^ r`. -/
theorem eq_pow (X : ShiftedExactCouple S T) (r : ℕ) :
    X.tAlphaSource r = (T ^ (r : ℤ)).functor.obj X.A := sorry

end TAlphaSource

/-- The forward composite `Tα ≫ T²α ≫ ... ≫ Tʳα`, represented as the shared algebra fold of
`tAlpha` from its iterated `T`-translate to `A`. The zeroth iterate is the identity. -/
@[stacks 0AMJ "forward translated outer-map iterate"]
abbrev tAlphaIterate (X : ShiftedExactCouple S T) (r : ℕ) : X.tAlphaSource r ⟶ X.A :=
  Endofunctor.iterate.fold T.functor X.tAlpha r

namespace TAlphaIterate

/-- The zeroth forward translated outer map is the identity of `A`. -/
@[simp]
theorem zero (X : ShiftedExactCouple S T) :
    X.tAlphaIterate 0 = 𝟙 X.A := sorry

/-- The successor forward translated outer map is obtained by mapping the preceding iterate by
`T` and postcomposing with `tAlpha`. -/
@[simp]
theorem succ (X : ShiftedExactCouple S T) (r : ℕ) :
    X.tAlphaIterate (r + 1) = T.functor.map (X.tAlphaIterate r) ≫ X.tAlpha := sorry

/-- A shifted-exact-couple morphism commutes with the forward translated outer-map iterates.
This is the exact-couple specialization of `Endofunctor.iterate.fold_naturality`. -/
@[stacks 0AMJ "naturality of forward translated outer-map iterates"]
theorem naturality {X Y : ShiftedExactCouple S T} (φ : Hom X Y) (r : ℕ) :
    (Endofunctor.iterate T.functor r).map φ.a ≫ Y.tAlphaIterate r =
      X.tAlphaIterate r ≫ φ.a := sorry

end TAlphaIterate

/-- The target of the `r`-fold backward translated outer map, expressed through the shared
zero-based endofunctor iterate of `T.inverse`. -/
@[stacks 0AMJ "backward translated outer-map target"]
abbrev alphaTarget (X : ShiftedExactCouple S T) (r : ℕ) : C :=
  (Endofunctor.iterate T.inverse r).obj X.A

namespace AlphaTarget

/-- The target of the zeroth backward translated outer map is `A`. -/
@[simp]
theorem zero (X : ShiftedExactCouple S T) :
    X.alphaTarget 0 = X.A := sorry

/-- The target of the successor backward translated outer map is one further inverse translate. -/
@[simp]
theorem succ (X : ShiftedExactCouple S T) (r : ℕ) :
    X.alphaTarget (r + 1) = T.inverse.obj (X.alphaTarget r) := sorry

/-- The recursively bracketed target is the object obtained from the canonical power `T ^ (-r)`. -/
theorem eq_pow (X : ShiftedExactCouple S T) (r : ℕ) :
    X.alphaTarget r = (T ^ (-(r : ℤ))).functor.obj X.A := sorry

end AlphaTarget

/-- The backward composite `α ≫ T⁻¹α ≫ ... ≫ T⁻ʳ⁺¹α`, represented as the shared coalgebra
unfold of `α` from `A` to its iterated `T⁻¹`-translate. The zeroth iterate is the identity. -/
@[stacks 0AMJ "backward translated outer-map iterate"]
abbrev alphaIterate (X : ShiftedExactCouple S T) (r : ℕ) : X.A ⟶ X.alphaTarget r :=
  Endofunctor.iterate.unfold T.inverse X.α r

namespace AlphaIterate

/-- The zeroth backward translated outer map is the identity of `A`. -/
@[simp]
theorem zero (X : ShiftedExactCouple S T) :
    X.alphaIterate 0 = 𝟙 X.A := sorry

/-- The successor backward translated outer map is obtained by postcomposing `α` with the inverse
translate of the preceding iterate. -/
@[simp]
theorem succ (X : ShiftedExactCouple S T) (r : ℕ) :
    X.alphaIterate (r + 1) = X.α ≫ T.inverse.map (X.alphaIterate r) := sorry

/-- A shifted-exact-couple morphism commutes with the backward translated outer-map iterates.
This is the exact-couple specialization of `Endofunctor.iterate.unfold_naturality`. -/
@[stacks 0AMJ "naturality of backward translated outer-map iterates"]
theorem naturality {X Y : ShiftedExactCouple S T} (φ : Hom X Y) (r : ℕ) :
    φ.a ≫ Y.alphaIterate r =
      X.alphaIterate r ≫ (Endofunctor.iterate T.inverse r).map φ.a := sorry

end AlphaIterate

end Basic

section Filtration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S T : C ≌ C}

/-- The closed-form cycle subobject `f⁻¹(image (Tα ⋯ Tʳα))` on page `r + 1`. -/
@[stacks 0AMJ "shifted exact-couple cycle filtration"]
abbrev cyclesSubobject (X : ShiftedExactCouple S T) (r : ℕ) : Subobject X.E :=
  (Subobject.pullback X.f).obj (imageSubobject (X.tAlphaIterate r))

/-- The shifted closed-form boundary subobject `g(kernel (α ⋯ T⁻ʳ⁺¹α))` in `S E` on page
`r + 1`. This models `S B_{r+1}` directly, without choosing a transport of subobjects along `S`. -/
@[stacks 0AMJ "shifted exact-couple boundary filtration"]
abbrev shiftedBoundariesSubobject (X : ShiftedExactCouple S T) (r : ℕ) :
    Subobject (S.functor.obj X.E) :=
  imageSubobject ((kernelSubobject (X.alphaIterate r)).arrow ≫ X.g)

/-- 0AMJ (Remark 12.21.5, Variant) (1): the cycle filtration of the associated spectral sequence
is the inverse-image filtration defined by the forward translated outer maps. -/
@[stacks 0AMJ]
theorem Associated.cycle_eq
    (X : ShiftedExactCouple S T) (r : ℕ) :
    (Derived.associatedSpectralSequence X).cycle (Nat.succPNat r) =
      X.cyclesSubobject r := sorry

/-- 0AMJ (Remark 12.21.5, Variant) (2): after applying the shift `S`, the boundary filtration is
the image under `g` of the kernels of the backward translated outer maps. The left side uses the
image of the mapped subobject inclusion as the canonical formalization of `S B_{r+1}`. -/
@[stacks 0AMJ]
theorem Associated.boundary_map_eq
    (X : ShiftedExactCouple S T) (r : ℕ) :
    imageSubobject
        (S.functor.map
          ((Derived.associatedSpectralSequence X).boundary (Nat.succPNat r)).arrow) =
      X.shiftedBoundariesSubobject r := sorry

end Filtration

end ShiftedExactCouple
end CategoryTheory
