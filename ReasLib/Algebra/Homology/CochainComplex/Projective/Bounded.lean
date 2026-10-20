/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.CategoryTheory.Preadditive.Projective.Closure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded complexes of projective objects

This file owns the fixed-interval representative used by projective-amplitude statements.  The
support bounds and termwise projectivity are carried by the bundled object, so downstream APIs can
use the corresponding instances without rebuilding local `letI` declarations.
@stack 0A5N
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- Definition 15.69.1 (0A5N): complexes supported in `[a, b]` with projective terms. -/
@[stacks 0A5N "bounded projective representative"]
def projectiveIn (a b : ℤ) : ObjectProperty (CochainComplex C ℤ) :=
  (strictlyGE C a ⊓ strictlyLE C b) ⊓
    termsIn (isProjective C)

/-- Membership in `projectiveIn C a b` is the explicit support-and-termwise formulation. -/
@[stacks 0A5N "membership in bounded projective representatives"]
theorem mem_projectiveIn_iff (P : CochainComplex C ℤ) (a b : ℤ) :
    projectiveIn C a b P ↔
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i) := sorry

/-- The full subcategory of complexes of projectives supported in `[a, b]`. -/
@[stacks 0A5N "bounded projective representatives"]
abbrev ProjectiveIn (a b : ℤ) :=
  (projectiveIn C a b).FullSubcategory

namespace ProjectiveIn

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {a b : ℤ}

/-- Bundle a complex together with the support and termwise-projectivity conditions. -/
@[stacks 0A5N "constructor for bounded projective representatives"]
def of (P : CochainComplex C ℤ) (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hproj : ∀ i : ℤ, Projective (P.X i)) : ProjectiveIn C a b :=
  ⟨P, (mem_projectiveIn_iff C P a b).2 ⟨hGE, hLE, hproj⟩⟩

/-- The bounded-projective constructor retains the supplied cochain complex. -/
@[simp, stacks 0A5N "underlying complex of a bounded projective representative"]
theorem of_obj (P : CochainComplex C ℤ) (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hproj : ∀ i : ℤ, Projective (P.X i)) :
    (of P hGE hLE hproj).obj = P := sorry

/-- The canonical inclusion of bounded projective complexes into all cochain complexes. -/
@[stacks 0A5N "inclusion of bounded projective representatives"]
abbrev ι (a b : ℤ) : ProjectiveIn C a b ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι _

/-- A bundled projective representative carries its lower support bound. -/
@[stacks 0A5N "lower bound of a bounded projective representative"]
instance isStrictlyGE (P : ProjectiveIn C a b) :
    P.obj.IsStrictlyGE a := sorry

/-- A bundled projective representative carries its upper support bound. -/
@[stacks 0A5N "upper bound of a bounded projective representative"]
instance isStrictlyLE (P : ProjectiveIn C a b) :
    P.obj.IsStrictlyLE b := sorry

/-- Every term of a bundled projective representative is projective. -/
@[stacks 0A5N "termwise projectivity of a bounded representative"]
instance projective (P : ProjectiveIn C a b) (i : ℤ) :
    Projective (P.obj.X i) := sorry

/-- A bounded projective representative is stable under isomorphism of complexes. -/
@[stacks 0A5N "isomorphism stability of bounded projective representatives"]
instance isClosedUnderIsomorphisms (a b : ℤ) :
    (projectiveIn C a b).IsClosedUnderIsomorphisms := sorry

end ProjectiveIn

end CochainComplex
