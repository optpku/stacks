/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme structures on closed subsets

Mathlib's `Scheme.IdealSheafData` is the canonical data owner for a closed
subscheme. This file packages the fiber of its support map over one prescribed
closed subset, without duplicating the associated scheme or immersion.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme structure on a closed subset `Z` is ideal-sheaf data whose support is `Z`. -/
@[stacks 01J4 "scheme structure on a closed subset"]
structure ClosedSubschemeStructure {X : Scheme.{u}} (Z : Closeds X) where
  /-- The ideal sheaf defining the closed subscheme. -/
  ideal : X.IdealSheafData
  /-- The defining ideal sheaf has the prescribed support. -/
  support_eq : ideal.support = Z

attribute [simp] ClosedSubschemeStructure.support_eq

namespace ClosedSubschemeStructure

variable {X : Scheme.{u}} {Z : Closeds X}

/-- Ideal-sheaf data regarded as a scheme structure on its own support. -/
@[stacks 01J4 "ideal-sheaf data as a fixed-support scheme structure"]
def ofIdeal (I : X.IdealSheafData) : ClosedSubschemeStructure I.support where
  ideal := I
  support_eq := rfl

/-- The ideal underlying the fixed-support structure associated to `I` is `I`. -/
@[simp]
theorem ofIdeal_ideal (I : X.IdealSheafData) :
    (ofIdeal I).ideal = I := sorry

/-- Scheme structures on a fixed closed subset are equal when their defining ideal sheaves
are equal. -/
@[ext]
theorem ext {T T' : ClosedSubschemeStructure Z} (h : T.ideal = T'.ideal) :
    T = T' := sorry

/-- The closed subscheme carried by a scheme structure on a closed subset. -/
@[stacks 01J4 "fixed-support closed subscheme"]
noncomputable abbrev subscheme (T : ClosedSubschemeStructure Z) : Scheme.{u} :=
  T.ideal.subscheme

/-- The canonical closed immersion associated to a scheme structure on a closed subset. -/
@[stacks 01J4 "fixed-support closed immersion"]
noncomputable abbrev ι (T : ClosedSubschemeStructure Z) : T.subscheme ⟶ X :=
  T.ideal.subschemeι

/-- The canonical immersion has the prescribed closed subset as its range. -/
@[simp, stacks 01J4 "fixed-support immersion range"]
theorem range_ι (T : ClosedSubschemeStructure Z) :
    Set.range T.ι = Z := sorry

/-- The kernel ideal of the canonical immersion is the defining ideal sheaf. -/
@[simp, stacks 01J4 "fixed-support immersion kernel"]
theorem ker_ι (T : ClosedSubschemeStructure Z) :
    T.ι.ker = T.ideal := sorry

end ClosedSubschemeStructure

end AlgebraicGeometry.Scheme
