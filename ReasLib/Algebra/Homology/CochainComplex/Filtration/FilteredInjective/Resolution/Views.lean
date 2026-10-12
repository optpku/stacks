/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Target
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Bounded

/-!
# Functorial Views of Strict Filtered-Injective Resolution Targets

This leaf applies the canonical bounded homotopy quotient, graded-piece, and forgetful functors
to the explicit bounded target of a strict filtered-injective resolution.  Objects and morphisms
are defined only by applying existing functors to `Resolution.target`, `Resolution.comparison`,
and `Resolution.Map.targetMap`; no resolutions, lifts, or representatives are chosen here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open FilteredObject.Finite.Plus

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus.Resolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## Bounded homotopy view -/

/-- The bounded target of a strict filtered-injective resolution in the bounded-below homotopy
category of finite filtered objects. -/
@[stacks 05TW "bounded homotopy target of a strict filtered-injective resolution"]
noncomputable abbrev targetHomotopy
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    HomotopyCategory.Plus (FilteredObject.Finite.category C) :=
  (HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)).obj R.target

/-- The resolution comparison after passing to the bounded-below homotopy category of finite
filtered objects. -/
@[stacks 05TW "bounded homotopy comparison of a strict filtered-injective resolution"]
noncomputable abbrev homotopyComparison
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    (HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)).obj K ⟶
      R.targetHomotopy :=
  (HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)).map R.comparison

namespace Map

/-- The map between bounded homotopy targets induced by a map of strict filtered-injective
resolutions. -/
@[stacks 05TU "bounded homotopy target map of strict filtered-injective resolutions"]
noncomputable abbrev homotopyMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    R.targetHomotopy ⟶ S.targetHomotopy :=
  (HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)).map m.targetMap

/-- Bounded homotopy target maps commute with the two homotopy resolution comparisons. -/
@[reassoc, stacks 05TU "naturality of bounded homotopy resolution comparisons"]
theorem homotopyComparison_naturality
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    R.homotopyComparison ≫ m.homotopyMap =
      (HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)).map f ≫
        S.homotopyComparison := sorry

/-- The homotopy target map induced by the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity bounded homotopy target map"]
theorem id_homotopyMap {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : (id R).homotopyMap = 𝟙 R.targetHomotopy := sorry

/-- Homotopy target maps preserve composition of resolution maps. -/
@[simp, stacks 05TU "composition of bounded homotopy target maps"]
theorem comp_homotopyMap
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    (comp m n).homotopyMap = m.homotopyMap ≫ n.homotopyMap := sorry

/-- Reindexing a resolution map does not change its homotopy target map. -/
@[simp, stacks 05TU "reindexing a bounded homotopy target map"]
theorem reindex_homotopyMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    (reindex h m).homotopyMap = m.homotopyMap := sorry

end Map

/-! ## Graded-piece views -/

/-- The `p`-th graded piece of the bounded target of a strict filtered-injective resolution. -/
@[stacks 05TW "graded-piece target of a strict filtered-injective resolution"]
noncomputable abbrev gradedPiece
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) (p : ℤ) :
    CochainComplex.Plus C :=
  (GradedPiece.cochain C p).obj R.target

/-- The comparison on the `p`-th graded pieces of a strict filtered-injective resolution. -/
@[stacks 05TW "graded-piece comparison of a strict filtered-injective resolution"]
noncomputable abbrev gradedPieceComparison
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) (p : ℤ) :
    (GradedPiece.cochain C p).obj K ⟶ R.gradedPiece p :=
  (GradedPiece.cochain C p).map R.comparison

namespace Map

/-- The map on `p`-th graded-piece targets induced by a map of strict filtered-injective
resolutions. -/
@[stacks 05TU "graded-piece target map of strict filtered-injective resolutions"]
noncomputable abbrev gradedPieceMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) (p : ℤ) :
    R.gradedPiece p ⟶ S.gradedPiece p :=
  (GradedPiece.cochain C p).map m.targetMap

/-- Graded-piece target maps commute with the two graded-piece resolution comparisons. -/
@[reassoc, stacks 05TU "naturality of graded-piece resolution comparisons"]
theorem gradedPieceComparison_naturality
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) (p : ℤ) :
    R.gradedPieceComparison p ≫ m.gradedPieceMap p =
      (GradedPiece.cochain C p).map f ≫ S.gradedPieceComparison p := sorry

/-- The graded-piece target map induced by the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity graded-piece target map"]
theorem id_gradedPieceMap
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) (p : ℤ) :
    (id R).gradedPieceMap p = 𝟙 (R.gradedPiece p) := sorry

/-- Graded-piece target maps preserve composition of resolution maps. -/
@[simp, stacks 05TU "composition of graded-piece target maps"]
theorem comp_gradedPieceMap
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) (p : ℤ) :
    (comp m n).gradedPieceMap p = m.gradedPieceMap p ≫ n.gradedPieceMap p := sorry

/-- Reindexing a resolution map does not change its graded-piece target map. -/
@[simp, stacks 05TU "reindexing a graded-piece target map"]
theorem reindex_gradedPieceMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) (p : ℤ) :
    (reindex h m).gradedPieceMap p = m.gradedPieceMap p := sorry

end Map

/-! ## Graded-piece homotopy views -/

/-- The `p`-th graded piece of a strict filtered-injective resolution target in the bounded-below
homotopy category. -/
@[stacks 05TW "graded-piece homotopy target of a strict filtered-injective resolution"]
noncomputable abbrev gradedPieceHomotopy
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) (p : ℤ) :
    HomotopyCategory.Plus C :=
  (GradedPiece.homotopy C p).obj R.target

/-- The `p`-th graded-piece resolution comparison in the bounded-below homotopy category. -/
@[stacks 05TW "graded-piece homotopy comparison of a strict filtered-injective resolution"]
noncomputable abbrev gradedPieceHomotopyComparison
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) (p : ℤ) :
    (GradedPiece.homotopy C p).obj K ⟶ R.gradedPieceHomotopy p :=
  (GradedPiece.homotopy C p).map R.comparison

namespace Map

/-- The map on graded-piece homotopy targets induced by a map of strict filtered-injective
resolutions. -/
@[stacks 05TU "graded-piece homotopy target map of strict filtered-injective resolutions"]
noncomputable abbrev gradedPieceHomotopyMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) (p : ℤ) :
    R.gradedPieceHomotopy p ⟶ S.gradedPieceHomotopy p :=
  (GradedPiece.homotopy C p).map m.targetMap

/-- Graded-piece homotopy target maps commute with the two homotopy comparisons. -/
@[reassoc, stacks 05TU "naturality of graded-piece homotopy resolution comparisons"]
theorem gradedPieceHomotopyComparison_naturality
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) (p : ℤ) :
    R.gradedPieceHomotopyComparison p ≫ m.gradedPieceHomotopyMap p =
      (GradedPiece.homotopy C p).map f ≫ S.gradedPieceHomotopyComparison p := sorry

/-- The graded-piece homotopy map induced by the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity graded-piece homotopy target map"]
theorem id_gradedPieceHomotopyMap
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) (p : ℤ) :
    (id R).gradedPieceHomotopyMap p = 𝟙 (R.gradedPieceHomotopy p) := sorry

/-- Graded-piece homotopy maps preserve composition of resolution maps. -/
@[simp, stacks 05TU "composition of graded-piece homotopy target maps"]
theorem comp_gradedPieceHomotopyMap
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) (p : ℤ) :
    (comp m n).gradedPieceHomotopyMap p =
      m.gradedPieceHomotopyMap p ≫ n.gradedPieceHomotopyMap p := sorry

/-- Reindexing a resolution map does not change its graded-piece homotopy map. -/
@[simp, stacks 05TU "reindexing a graded-piece homotopy target map"]
theorem reindex_gradedPieceHomotopyMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) (p : ℤ) :
    (reindex h m).gradedPieceHomotopyMap p = m.gradedPieceHomotopyMap p := sorry

end Map

/-! ## Underlying-complex views -/

/-- The bounded underlying cochain complex of a strict filtered-injective resolution target. -/
@[stacks 05TW "underlying target of a strict filtered-injective resolution"]
noncomputable abbrev underlying
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    CochainComplex.Plus C :=
  (Forget.cochain C).obj R.target

/-- The resolution comparison after forgetting the finite filtrations. -/
@[stacks 05TW "underlying comparison of a strict filtered-injective resolution"]
noncomputable abbrev underlyingComparison
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    (Forget.cochain C).obj K ⟶ R.underlying :=
  (Forget.cochain C).map R.comparison

namespace Map

/-- The map on underlying bounded complexes induced by a map of strict filtered-injective
resolutions. -/
@[stacks 05TU "underlying target map of strict filtered-injective resolutions"]
noncomputable abbrev underlyingMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) : R.underlying ⟶ S.underlying :=
  (Forget.cochain C).map m.targetMap

/-- Underlying target maps commute with the two underlying resolution comparisons. -/
@[reassoc, stacks 05TU "naturality of underlying resolution comparisons"]
theorem underlyingComparison_naturality
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    R.underlyingComparison ≫ m.underlyingMap =
      (Forget.cochain C).map f ≫ S.underlyingComparison := sorry

/-- The underlying target map induced by the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity underlying target map"]
theorem id_underlyingMap {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : (id R).underlyingMap = 𝟙 R.underlying := sorry

/-- Underlying target maps preserve composition of resolution maps. -/
@[simp, stacks 05TU "composition of underlying target maps"]
theorem comp_underlyingMap
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    (comp m n).underlyingMap = m.underlyingMap ≫ n.underlyingMap := sorry

/-- Reindexing a resolution map does not change its underlying target map. -/
@[simp, stacks 05TU "reindexing an underlying target map"]
theorem reindex_underlyingMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    (reindex h m).underlyingMap = m.underlyingMap := sorry

end Map

/-! ## Underlying homotopy views -/

/-- The underlying target of a strict filtered-injective resolution in the bounded-below
homotopy category. -/
@[stacks 05TW "underlying homotopy target of a strict filtered-injective resolution"]
noncomputable abbrev underlyingHomotopy
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    HomotopyCategory.Plus C :=
  (Forget.homotopy C).obj R.target

/-- The underlying resolution comparison in the bounded-below homotopy category. -/
@[stacks 05TW "underlying homotopy comparison of a strict filtered-injective resolution"]
noncomputable abbrev underlyingHomotopyComparison
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    (Forget.homotopy C).obj K ⟶ R.underlyingHomotopy :=
  (Forget.homotopy C).map R.comparison

namespace Map

/-- The map on underlying homotopy targets induced by a map of strict filtered-injective
resolutions. -/
@[stacks 05TU "underlying homotopy target map of strict filtered-injective resolutions"]
noncomputable abbrev underlyingHomotopyMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    R.underlyingHomotopy ⟶ S.underlyingHomotopy :=
  (Forget.homotopy C).map m.targetMap

/-- Underlying homotopy target maps commute with the two homotopy comparisons. -/
@[reassoc, stacks 05TU "naturality of underlying homotopy resolution comparisons"]
theorem underlyingHomotopyComparison_naturality
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    R.underlyingHomotopyComparison ≫ m.underlyingHomotopyMap =
      (Forget.homotopy C).map f ≫ S.underlyingHomotopyComparison := sorry

/-- The underlying homotopy map induced by the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity underlying homotopy target map"]
theorem id_underlyingHomotopyMap
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    (id R).underlyingHomotopyMap = 𝟙 R.underlyingHomotopy := sorry

/-- Underlying homotopy maps preserve composition of resolution maps. -/
@[simp, stacks 05TU "composition of underlying homotopy target maps"]
theorem comp_underlyingHomotopyMap
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    (comp m n).underlyingHomotopyMap =
      m.underlyingHomotopyMap ≫ n.underlyingHomotopyMap := sorry

/-- Reindexing a resolution map does not change its underlying homotopy map. -/
@[simp, stacks 05TU "reindexing an underlying homotopy target map"]
theorem reindex_underlyingHomotopyMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    (reindex h m).underlyingHomotopyMap = m.underlyingHomotopyMap := sorry

end Map

end CochainComplex.FilteredInjectivePlus.Resolution
