/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.PageTower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism Transport for Homology Page Towers

The pagewise and subquotient constructions attached to a `HomologyPageTower` preserve
isomorphisms.  This module contains only the transport instances; the data and naturality owners
remain in `PageTower` so clients can import exactly the layer they need.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologyPageTower

namespace Hom

/-- A page component of an isomorphism of homology-page towers is an isomorphism. -/
@[stacks 011O "isomorphism on a homology-page tower component"]
noncomputable instance app_isIso {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+)
    [IsIso f] : IsIso (f.app r) := sorry

end Hom

namespace PageCycle

/-- Restriction to page cycles preserves isomorphisms of homology-page towers. -/
@[stacks 011O "isomorphism on page-cycle objects"]
noncomputable instance map_isIso {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+)
    [IsIso f] : IsIso (map f r) := sorry

end PageCycle

namespace PageBoundary

/-- Restriction to page boundaries preserves isomorphisms of homology-page towers. -/
@[stacks 011O "isomorphism on page-boundary objects"]
noncomputable instance map_isIso {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+)
    [IsIso f] : IsIso (map f r) := sorry

end PageBoundary

namespace PageHomology

/-- The local homology quotient map of a tower is an isomorphism when the tower map is. -/
@[stacks 011O "isomorphism on local page homology"]
noncomputable instance map_isIso {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+)
    [IsIso f] : IsIso (map f r) := sorry

end PageHomology

namespace Cycle

/-- Restriction to recursive cycle stages preserves tower isomorphisms. -/
@[stacks 011O "isomorphism on recursive cycle stages"]
noncomputable instance map_isIso {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+)
    [IsIso f] : IsIso (map f r) := sorry

end Cycle

namespace Boundary

/-- Restriction to recursive boundary stages preserves tower isomorphisms. -/
@[stacks 011O "isomorphism on recursive boundary stages"]
noncomputable instance map_isIso {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+)
    [IsIso f] : IsIso (map f r) := sorry

end Boundary

namespace PageQuotient

/-- The recursive page quotient map of a tower is an isomorphism when the tower map is. -/
@[stacks 011O "isomorphism on recursive page quotients"]
noncomputable instance map_isIso {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+)
    [IsIso f] : IsIso (map f r) := sorry

end PageQuotient

variable {P Q : HomologyPageTower C} (f : P ⟶ Q) [IsIso f]

#synth IsIso (f.app 1)
#synth IsIso (PageCycle.map f 1)
#synth IsIso (PageBoundary.map f 1)
#synth IsIso (PageHomology.map f 1)
#synth IsIso (Cycle.map f 1)
#synth IsIso (Boundary.map f 1)
#synth IsIso (PageQuotient.map f 1)

end HomologyPageTower

end CategoryTheory
