module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.GE
public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.LE
public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.Support

/-!
# Canonical Bounded Replacement Square

This file packages the deterministic diagram obtained by first taking good upper and lower
filtered truncations and then lower-truncating the upper representative.  Objects and arrows are
explicit; finiteness, support, commutativity, and quasi-isomorphism remain separate propositions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Replace.Square

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Bounded

/-- The bounded vertex of the canonical replacement square. -/
@[stacks 05S5 "filtered bounded replacement square"]
noncomputable def obj (K : FilteredComplex A) (a b : ℤ) : FilteredComplex A :=
  truncGE (truncLE K b) a

/-- The canonical map from the bounded-above vertex to the bounded vertex. -/
@[stacks 05S5 "filtered bounded replacement square"]
noncomputable def fromLE (K : FilteredComplex A) (a b : ℤ) :
    truncLE K b ⟶ obj K a b :=
  πTruncGE (truncLE K b) a

/-- The canonical comparison map from the bounded vertex to the bounded-below vertex. -/
@[stacks 05S5 "filtered bounded replacement square"]
noncomputable def toGE (K : FilteredComplex A) (a b : ℤ) : obj K a b ⟶ truncGE K a :=
  TruncGE.desc a (ιTruncLE K b ≫ πTruncGE K a) (TruncGE.isStrictlyGE K a)

/-- The bounded vertex retains termwise finite filtrations. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem finite (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a b : ℤ) :
    (obj K a b).HasFiniteFiltrations := sorry

/-- The bounded vertex is strictly bounded below after forgetting the filtration. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem isStrictlyGE (K : FilteredComplex A) (a b : ℤ) :
    (obj K a b).underlying.IsStrictlyGE a := sorry

/-- The bounded vertex is strictly bounded above after forgetting the filtration. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem isStrictlyLE (K : FilteredComplex A) (a b : ℤ) :
    (obj K a b).underlying.IsStrictlyLE b := sorry

/-- The three canonical vertices and four canonical maps form a commutative square. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem comm (K : FilteredComplex A) (a b : ℤ) :
    CommSq (fromLE K a b) (ιTruncLE K b) (toGE K a b) (πTruncGE K a) := sorry

/-- Under two-sided associated-graded support, the map from the bounded-above vertex to the
bounded vertex is a filtered quasi-isomorphism. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem quasiIso_fromLE (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a b : ℤ)
    (hGE : K.associatedGraded.IsGE a) (hLE : K.associatedGraded.IsLE b) :
    _root_.QuasiIso (associatedGradedMap (fromLE K a b)) := sorry

/-- Under two-sided associated-graded support, the comparison from the bounded vertex to the
bounded-below vertex is a filtered quasi-isomorphism. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem quasiIso_toGE (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a b : ℤ)
    (hGE : K.associatedGraded.IsGE a) (hLE : K.associatedGraded.IsLE b) :
    _root_.QuasiIso (associatedGradedMap (toGE K a b)) := sorry

end Bounded

end CategoryTheory.FilteredComplex.Replace.Square
