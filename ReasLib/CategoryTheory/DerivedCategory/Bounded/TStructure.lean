/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Canonical T-Structures on Bounded Derived Categories

@stack 05RU
@stack 05RR

This module restricts the canonical derived t-structure to `D⁻(C)` and
`Dᵇ(C)`.  It mirrors Mathlib's `DerivedCategory.Plus` API so downstream code
can state bounds, homology vanishing, and conservativity without repeatedly
passing through the fully faithful inclusion into `DerivedCategory C`.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Triangulated
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C]

namespace DerivedCategory.Minus

/-- The canonical t-structure on the bounded-above derived category. -/
@[stacks 05RU "bounded-above derived t-structure"]
noncomputable abbrev TStructure.t : TStructure (DerivedCategory.Minus C) :=
  (DerivedCategory.TStructure.t (C := C)).minus.tStructure
    DerivedCategory.TStructure.t

/-- The assertion that a bounded-above derived object is cohomologically at
least `n`. -/
@[stacks 05RU "bounded-above lower cohomological bound"]
abbrev IsGE (X : DerivedCategory.Minus C) (n : ℤ) : Prop :=
  TStructure.t.IsGE X n

/-- The assertion that a bounded-above derived object is cohomologically at
most `n`. -/
@[stacks 05RU "bounded-above upper cohomological bound"]
abbrev IsLE (X : DerivedCategory.Minus C) (n : ℤ) : Prop :=
  TStructure.t.IsLE X n

/-- A lower bound in `D⁻(C)` is equivalent to the same lower bound after
inclusion into `DerivedCategory C`. -/
@[stacks 05RU]
theorem isGE_ι_obj_iff (X : DerivedCategory.Minus C) (n : ℤ) :
    (DerivedCategory.Minus.ι.obj X).IsGE n ↔ X.IsGE n := sorry

/-- An upper bound in `D⁻(C)` is equivalent to the same upper bound after
inclusion into `DerivedCategory C`. -/
@[stacks 05RU]
theorem isLE_ι_obj_iff (X : DerivedCategory.Minus C) (n : ℤ) :
    (DerivedCategory.Minus.ι.obj X).IsLE n ↔ X.IsLE n := sorry

/-- Lower bounds on bounded-above derived objects are inherited by their
ambient derived objects. -/
instance ι_obj_isGE (X : DerivedCategory.Minus C) (n : ℤ) [X.IsGE n] :
    (DerivedCategory.Minus.ι.obj X).IsGE n := sorry

/-- Upper bounds on bounded-above derived objects are inherited by their
ambient derived objects. -/
instance ι_obj_isLE (X : DerivedCategory.Minus C) (n : ℤ) [X.IsLE n] :
    (DerivedCategory.Minus.ι.obj X).IsLE n := sorry

/-- An object concentrated in degree `n` is bounded below by `n` in
`D⁻(C)`. -/
instance singleFunctor.isGE (X : C) (n : ℤ) :
    ((singleFunctor C n).obj X).IsGE n := sorry

/-- An object concentrated in degree `n` is bounded above by `n` in
`D⁻(C)`. -/
instance singleFunctor.isLE (X : C) (n : ℤ) :
    ((singleFunctor C n).obj X).IsLE n := sorry

/-- Cohomology below a lower bound vanishes in `D⁻(C)`. -/
@[stacks 05RU]
theorem isZero_homology_of_isGE (X : DerivedCategory.Minus C) (n : ℤ)
    [X.IsGE n] (i : ℤ) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj X) := sorry

/-- Cohomology above an upper bound vanishes in `D⁻(C)`. -/
@[stacks 05RU]
theorem isZero_homology_of_isLE (X : DerivedCategory.Minus C) (n : ℤ)
    [X.IsLE n] (i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj X) := sorry

/-- A morphism in `D⁻(C)` is an isomorphism exactly when it induces
isomorphisms on cohomology in every degree. -/
@[stacks 05RR]
theorem isIso_iff {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ n : ℤ, IsIso ((homologyFunctor C n).map f) := sorry

end DerivedCategory.Minus

namespace DerivedCategory.Bounded

/-- The canonical t-structure on the bounded derived category. -/
@[stacks 05RU "bounded derived t-structure"]
noncomputable abbrev TStructure.t : TStructure (DerivedCategory.Bounded C) :=
  (DerivedCategory.TStructure.t (C := C)).bounded.tStructure
    DerivedCategory.TStructure.t

/-- The assertion that a bounded derived object is cohomologically at least
`n`. -/
@[stacks 05RU "bounded lower cohomological bound"]
abbrev IsGE (X : DerivedCategory.Bounded C) (n : ℤ) : Prop :=
  TStructure.t.IsGE X n

/-- The assertion that a bounded derived object is cohomologically at most
`n`. -/
@[stacks 05RU "bounded upper cohomological bound"]
abbrev IsLE (X : DerivedCategory.Bounded C) (n : ℤ) : Prop :=
  TStructure.t.IsLE X n

/-- A lower bound in `Dᵇ(C)` is equivalent to the same lower bound after
inclusion into `DerivedCategory C`. -/
@[stacks 05RU]
theorem isGE_ι_obj_iff (X : DerivedCategory.Bounded C) (n : ℤ) :
    (DerivedCategory.Bounded.ι.obj X).IsGE n ↔ X.IsGE n := sorry

/-- An upper bound in `Dᵇ(C)` is equivalent to the same upper bound after
inclusion into `DerivedCategory C`. -/
@[stacks 05RU]
theorem isLE_ι_obj_iff (X : DerivedCategory.Bounded C) (n : ℤ) :
    (DerivedCategory.Bounded.ι.obj X).IsLE n ↔ X.IsLE n := sorry

/-- Lower bounds on bounded derived objects are inherited by their ambient
derived objects. -/
instance ι_obj_isGE (X : DerivedCategory.Bounded C) (n : ℤ) [X.IsGE n] :
    (DerivedCategory.Bounded.ι.obj X).IsGE n := sorry

/-- Upper bounds on bounded derived objects are inherited by their ambient
derived objects. -/
instance ι_obj_isLE (X : DerivedCategory.Bounded C) (n : ℤ) [X.IsLE n] :
    (DerivedCategory.Bounded.ι.obj X).IsLE n := sorry

/-- An object concentrated in degree `n` is bounded below by `n` in
`Dᵇ(C)`. -/
instance singleFunctor.isGE (X : C) (n : ℤ) :
    ((singleFunctor C n).obj X).IsGE n := sorry

/-- An object concentrated in degree `n` is bounded above by `n` in
`Dᵇ(C)`. -/
instance singleFunctor.isLE (X : C) (n : ℤ) :
    ((singleFunctor C n).obj X).IsLE n := sorry

/-- Cohomology below a lower bound vanishes in `Dᵇ(C)`. -/
@[stacks 05RU]
theorem isZero_homology_of_isGE (X : DerivedCategory.Bounded C) (n : ℤ)
    [X.IsGE n] (i : ℤ) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj X) := sorry

/-- Cohomology above an upper bound vanishes in `Dᵇ(C)`. -/
@[stacks 05RU]
theorem isZero_homology_of_isLE (X : DerivedCategory.Bounded C) (n : ℤ)
    [X.IsLE n] (i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj X) := sorry

/-- A morphism in `Dᵇ(C)` is an isomorphism exactly when it induces
isomorphisms on cohomology in every degree. -/
@[stacks 05RR]
theorem isIso_iff {X Y : DerivedCategory.Bounded C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ n : ℤ, IsIso ((homologyFunctor C n).map f) := sorry

end DerivedCategory.Bounded

end CategoryTheory
