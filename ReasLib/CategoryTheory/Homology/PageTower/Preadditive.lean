module

public import ReasLib.CategoryTheory.Homology.PageTower
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Structure on Homology Page Towers

Morphisms of homology-page towers are added pagewise.  The factorization and compatibility fields
are proposition-valued coherence data, so the public operations expose only the concrete page
maps and defer those laws.  This keeps the tower category reusable for spectral-sequence and
shifted-homology constructions without rebuilding local additive structures.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologyPageTower

variable {P Q : HomologyPageTower C}

namespace Hom

/-! The page-indexed family is the canonical extensionality carrier for tower morphisms. -/

/-- The pagewise components of a homology-page-tower morphism, with the index explicit. -/
@[stacks 011O "pagewise components of a homology-page tower morphism"]
abbrev appMap (f : P ⟶ Q) :
    ∀ r : ℕ+, P.page r ⟶ Q.page r :=
  fun r ↦ f.app r

/-- A tower morphism is determined by all of its pagewise components. -/
@[stacks 011O "homology-page tower morphism extensionality"]
theorem appMap_injective : Function.Injective (appMap (P := P) (Q := Q)) := sorry

/-- Zero morphisms of homology-page towers are defined pagewise. -/
@[stacks 011O "zero homology-page tower morphism"]
instance homZero : Zero (P ⟶ Q) where
  zero :=
    { app := fun _ ↦ 0
      pageCycle_factors := sorry
      pageBoundary_factors := sorry
      toNext_comm := sorry
      pageBoundary_map_comp_ofLE := sorry
      cycle_factors := sorry
      boundary_factors := sorry
      boundary_map_comp_ofLE := sorry
      intersection_factors := sorry
      intersection_map_comp_ofLE := sorry }

/-- Addition of homology-page-tower morphisms is defined pagewise. -/
@[stacks 011O "addition of homology-page tower morphisms"]
instance homAdd : Add (P ⟶ Q) where
  add f g :=
    { app := fun r ↦ f.app r + g.app r
      pageCycle_factors := sorry
      pageBoundary_factors := sorry
      toNext_comm := sorry
      pageBoundary_map_comp_ofLE := sorry
      cycle_factors := sorry
      boundary_factors := sorry
      boundary_map_comp_ofLE := sorry
      intersection_factors := sorry
      intersection_map_comp_ofLE := sorry }

/-- Negation of homology-page-tower morphisms is defined pagewise. -/
@[stacks 011O "negation of homology-page tower morphisms"]
instance homNeg : Neg (P ⟶ Q) where
  neg f :=
    { app := fun r ↦ -f.app r
      pageCycle_factors := sorry
      pageBoundary_factors := sorry
      toNext_comm := sorry
      pageBoundary_map_comp_ofLE := sorry
      cycle_factors := sorry
      boundary_factors := sorry
      boundary_map_comp_ofLE := sorry
      intersection_factors := sorry
      intersection_map_comp_ofLE := sorry }

/-- Subtraction of homology-page-tower morphisms is defined pagewise. -/
@[stacks 011O "subtraction of homology-page tower morphisms"]
instance homSub : Sub (P ⟶ Q) where
  sub f g :=
    { app := fun r ↦ f.app r - g.app r
      pageCycle_factors := sorry
      pageBoundary_factors := sorry
      toNext_comm := sorry
      pageBoundary_map_comp_ofLE := sorry
      cycle_factors := sorry
      boundary_factors := sorry
      boundary_map_comp_ofLE := sorry
      intersection_factors := sorry
      intersection_map_comp_ofLE := sorry }

/-- Natural-number scalar multiplication of tower morphisms is defined pagewise. -/
@[stacks 011O "natural scalar action on homology-page tower morphisms"]
instance homNatSMul : SMul ℕ (P ⟶ Q) where
  smul n f :=
    { app := fun r ↦ n • f.app r
      pageCycle_factors := sorry
      pageBoundary_factors := sorry
      toNext_comm := sorry
      pageBoundary_map_comp_ofLE := sorry
      cycle_factors := sorry
      boundary_factors := sorry
      boundary_map_comp_ofLE := sorry
      intersection_factors := sorry
      intersection_map_comp_ofLE := sorry }

/-- Integer scalar multiplication of tower morphisms is defined pagewise. -/
@[stacks 011O "integer scalar action on homology-page tower morphisms"]
instance homIntSMul : SMul ℤ (P ⟶ Q) where
  smul n f :=
    { app := fun r ↦ n • f.app r
      pageCycle_factors := sorry
      pageBoundary_factors := sorry
      toNext_comm := sorry
      pageBoundary_map_comp_ofLE := sorry
      cycle_factors := sorry
      boundary_factors := sorry
      boundary_map_comp_ofLE := sorry
      intersection_factors := sorry
      intersection_map_comp_ofLE := sorry }

/-- The pagewise component of the zero tower morphism is zero. -/
@[simp, stacks 011O "zero tower morphism component"]
theorem zero_app (r : ℕ+) : (0 : P ⟶ Q).app r = 0 := sorry

/-- The pagewise component of a sum of tower morphisms is the sum of components. -/
@[simp, stacks 011O "sum of tower morphism components"]
theorem add_app (f g : P ⟶ Q) (r : ℕ+) : (f + g).app r = f.app r + g.app r := sorry

/-- The pagewise component of a negated tower morphism is the negated component. -/
@[simp, stacks 011O "negated tower morphism component"]
theorem neg_app (f : P ⟶ Q) (r : ℕ+) : (-f).app r = -f.app r := sorry

/-- The pagewise component of a difference of tower morphisms is the difference of components. -/
@[simp, stacks 011O "difference of tower morphism components"]
theorem sub_app (f g : P ⟶ Q) (r : ℕ+) : (f - g).app r = f.app r - g.app r := sorry

/-- Natural-number scalar multiplication commutes with taking page components. -/
@[simp, stacks 011O "natural scalar action on tower components"]
theorem nsmul_app (n : ℕ) (f : P ⟶ Q) (r : ℕ+) : (n • f).app r = n • f.app r := sorry

/-- Integer scalar multiplication commutes with taking page components. -/
@[simp, stacks 011O "integer scalar action on tower components"]
theorem zsmul_app (n : ℤ) (f : P ⟶ Q) (r : ℕ+) : (n • f).app r = n • f.app r := sorry

/-- Homology-page-tower morphisms form an additive commutative group componentwise. -/
@[stacks 011O "additive group of homology-page tower morphisms"]
instance homAddCommGroup : AddCommGroup (P ⟶ Q) :=
  Function.Injective.addCommGroup
    (fun f : P ⟶ Q ↦ appMap (P := P) (Q := Q) f)
    (appMap_injective (P := P) (Q := Q))
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl)

end Hom

/-- The category of homology-page towers is preadditive in an abelian ambient category. -/
@[stacks 011O "preadditive category of homology-page towers"]
instance : Preadditive (HomologyPageTower C) where
  homGroup := fun P Q ↦ inferInstance
  add_comp := sorry
  comp_add := sorry

#synth Preadditive (HomologyPageTower C)

namespace PageFunctor

/-- Evaluation at a fixed page of a homology-page tower is additive. -/
@[stacks 011O "additivity of page evaluation"]
noncomputable instance functor_additive (r : ℕ+) :
    (pageFunctor C r).Additive := sorry

end PageFunctor

namespace PageHomology

/-- The local page-homology functor is additive in tower morphisms. -/
@[stacks 011O "additivity of page homology evaluation"]
noncomputable instance functor_additive (r : ℕ+) :
    (functor C r).Additive := sorry

end PageHomology

namespace Cycle

/-- Evaluation at a recursive cycle stage is additive in tower morphisms. -/
@[stacks 011O "additivity of recursive cycle evaluation"]
noncomputable instance functor_additive (r : ℕ+) :
    (functor C r).Additive := sorry

end Cycle

namespace Boundary

/-- Evaluation at a recursive boundary stage is additive in tower morphisms. -/
@[stacks 011O "additivity of recursive boundary evaluation"]
noncomputable instance functor_additive (r : ℕ+) :
    (functor C r).Additive := sorry

end Boundary

namespace PageQuotient

/-- Evaluation at a recursive page quotient is additive in tower morphisms. -/
@[stacks 011O "additivity of recursive page-quotient evaluation"]
noncomputable instance functor_additive (r : ℕ+) :
    (functor C r).Additive := sorry

end PageQuotient

#synth (pageFunctor C 1).Additive
#synth (PageHomology.functor C 1).Additive
#synth (Cycle.functor C 1).Additive
#synth (Boundary.functor C 1).Additive
#synth (PageQuotient.functor C 1).Additive

end HomologyPageTower

end CategoryTheory
