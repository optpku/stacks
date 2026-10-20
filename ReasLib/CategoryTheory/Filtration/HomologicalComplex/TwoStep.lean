/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Functors
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Two-Step Quotients of Filtered Homological Complexes

For a homological complex in filtered objects, this file constructs the canonical short exact
sequence

`0 ⟶ gradedPiece K (p + 1) ⟶ quotient K p ⟶ gradedPiece K p ⟶ 0`

and its connecting morphism in homology.  The construction is independent of the complex shape.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace CategoryTheory
namespace HomologicalComplex.Filtered
namespace TwoStep

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

/-- The order relation comparing filtration stages two steps apart. -/
theorem le (p : ℤ) : p ≤ p + 1 + 1 := sorry

namespace GradedPiece

/-- The categorical cokernel presentation of the `p`-th graded-piece complex. -/
noncomputable abbrev cokernel
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    HomologicalComplex C c :=
  Limits.cokernel (Stage.comparison K (lt_add_one p).le)

/-- The canonical associated-graded construction agrees with the categorical cokernel of the
successive-stage comparison. -/
noncomputable def cokernelIso
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    gradedPiece K p ≅ cokernel K p :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦
      (PreservesCokernel.iso (HomologicalComplex.eval C c i)
        (Stage.comparison K (lt_add_one p).le)).symm)
    sorry

end GradedPiece

/-- The two-step quotient complex `quotient K p`. -/
noncomputable def quotient
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    HomologicalComplex C c :=
  Limits.cokernel (Stage.comparison K (le p))

/-- The map on two-step quotient complexes induced by a filtered-complex morphism. -/
@[stacks 012D "map of two-step quotient complexes"]
noncomputable def quotientMap {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (p : ℤ) : quotient K p ⟶ quotient L p :=
  Limits.cokernel.map
    (Stage.comparison K (le p))
    (Stage.comparison L (le p))
    (Stage.map f (p + 1 + 1))
    (Stage.map f p)
    (Stage.Comparison.naturality f (le p))

/-- The quotient map commutes with the canonical cokernel projections. -/
@[reassoc, stacks 012D "two-step quotient map and cokernel projection"]
theorem quotientMap_comm {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (p : ℤ) :
    Limits.cokernel.π (Stage.comparison K (le p)) ≫ quotientMap f p =
      Stage.map f p ≫ Limits.cokernel.π (Stage.comparison L (le p)) := sorry

/-- The two-step quotient map induced by an identity is the identity. -/
@[simp, stacks 012D "identity map of two-step quotient complexes"]
theorem quotientMap_id (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    quotientMap (𝟙 K) p = 𝟙 (quotient K p) := sorry

/-- The two-step quotient map induced by a composite is the composite of the quotient maps. -/
@[simp, stacks 012D "composition of two-step quotient maps"]
theorem quotientMap_comp {K L M : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    quotientMap (f ≫ g) p = quotientMap f p ≫ quotientMap g p := sorry

/-- The successive-stage square defining `left K p`. -/
theorem left_condition
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    Stage.comparison K (lt_add_one (p + 1)).le ≫
        Stage.comparison K (lt_add_one p).le =
      (𝟙 _) ≫ Stage.comparison K (le p) := sorry

/-- The canonical map `left K p`. -/
noncomputable def left
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    gradedPiece K (p + 1) ⟶ quotient K p :=
  (GradedPiece.cokernelIso K (p + 1)).hom ≫
    Limits.cokernel.map
      (Stage.comparison K (lt_add_one (p + 1)).le)
      (Stage.comparison K (le p))
      (𝟙 _)
      (Stage.comparison K (lt_add_one p).le)
      (left_condition K p)

/-- The successive-stage square defining `right K p`. -/
theorem right_condition
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    Stage.comparison K (le p) ≫ (𝟙 _) =
      Stage.comparison K (lt_add_one (p + 1)).le ≫
        Stage.comparison K (lt_add_one p).le := sorry

/-- The canonical projection `right K p`. -/
noncomputable def right
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    quotient K p ⟶ gradedPiece K p :=
  Limits.cokernel.map
      (Stage.comparison K (le p))
      (Stage.comparison K (lt_add_one p).le)
      (Stage.comparison K (lt_add_one (p + 1)).le)
      (𝟙 _)
      (right_condition K p) ≫
    (GradedPiece.cokernelIso K p).inv

/-- The two canonical maps in the two-step quotient sequence compose to zero. -/
theorem left_comp_right
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    left K p ≫ right K p = 0 := sorry

/-- The left map of the two-step quotient sequence is natural in filtered-complex morphisms. -/
@[reassoc, stacks 012D "naturality of the left two-step quotient map"]
theorem left_naturality {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (p : ℤ) :
    HomologicalComplex.Filtered.gradedPieceMap f (p + 1) ≫ left L p =
      left K p ≫ quotientMap f p := sorry

/-- The right map of the two-step quotient sequence is natural in filtered-complex morphisms. -/
@[reassoc, stacks 012D "naturality of the right two-step quotient map"]
theorem right_naturality {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (p : ℤ) :
    quotientMap f p ≫ right L p =
      right K p ≫ HomologicalComplex.Filtered.gradedPieceMap f p := sorry

/-- The canonical two-step quotient short complex. -/
noncomputable def shortComplex
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (left K p) (right K p) (left_comp_right K p)

/-- The morphism of canonical two-step quotient short complexes induced by a filtered-complex
morphism. -/
@[stacks 012D "map of two-step quotient short complexes"]
noncomputable def map {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (p : ℤ) : shortComplex K p ⟶ shortComplex L p :=
  ShortComplex.homMk
    (HomologicalComplex.Filtered.gradedPieceMap f (p + 1))
    (quotientMap f p)
    (HomologicalComplex.Filtered.gradedPieceMap f p)
    (left_naturality f p)
    (right_naturality f p)

/-- The map of two-step quotient short complexes induced by an identity is the identity. -/
@[simp, stacks 012D "identity map of two-step quotient short complexes"]
theorem map_id (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    map (𝟙 K) p = 𝟙 (shortComplex K p) := sorry

/-- The map of two-step quotient short complexes induced by a composite is the composite of the
two maps. -/
@[simp, stacks 012D "composition of two-step quotient short-complex maps"]
theorem map_comp {K L M : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    map (f ≫ g) p = map f p ≫ map g p := sorry

/-- The functor sending a filtered homological complex to its `p`-th two-step quotient sequence. -/
@[stacks 012D "two-step quotient short-complex functor"]
noncomputable def functor (p : ℤ) :
    HomologicalComplex (FilteredObject C) c ⥤ ShortComplex (HomologicalComplex C c) where
  obj K := shortComplex K p
  map f := map f p
  map_id K := map_id K p
  map_comp f g := map_comp f g p

namespace Functor

/-- The `p`-th two-step quotient functor evaluates to the canonical short complex. -/
@[simp, stacks 012D "object of the two-step quotient short-complex functor"]
theorem obj (p : ℤ) (K : HomologicalComplex (FilteredObject C) c) :
    (functor p).obj K = shortComplex K p := sorry

/-- The `p`-th two-step quotient functor maps a filtered-complex morphism by the canonical
two-step quotient short-complex map. -/
@[simp, stacks 012D "map of the two-step quotient short-complex functor"]
theorem map {K L : HomologicalComplex (FilteredObject C) c} (f : K ⟶ L) (p : ℤ) :
    (functor p).map f = TwoStep.map f p := sorry

end Functor

/-- The canonical two-step quotient sequence is short exact. -/
@[stacks 012D "two-step quotient sequence of a filtered homological complex"]
theorem shortExact
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    (shortComplex K p).ShortExact := sorry

/-- The connecting morphism of the two-step quotient sequence. -/
@[stacks 012D "first-page boundary of a filtered homological complex"]
noncomputable def boundary
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ)
    {i j : ι} (hij : c.Rel i j) :
    (gradedPiece K p).homology i ⟶ (gradedPiece K (p + 1)).homology j :=
  (shortExact K p).δ i j hij

end TwoStep
end HomologicalComplex.Filtered
end CategoryTheory
