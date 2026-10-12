/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module

/-!
# Support bounds for enriched Hom complexes

The support of `Hom^•(K, L)` reverses the support direction of `K` and preserves that of `L`.
This file records both exact cutoff formulas and the corresponding bounded-above, bounded-below,
and bounded object-property API for complexes in any linear preadditive category.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CochainComplex.HomComplex

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {K L : CochainComplex C ℤ}

/-- If `K` is supported in degrees at least `a` and `L` in degrees at most `b`, then
`Hom^•(K, L)` is supported in degrees at most `b - a`. -/
@[stacks 0A8H "upper support bound for a module-valued Hom complex"]
theorem isStrictlyLE {a b : ℤ} (hK : K.IsStrictlyGE a) (hL : L.IsStrictlyLE b) :
    (moduleComplex R K L).IsStrictlyLE (b - a) := sorry
/- Proof strategy: apply `degreeIso` and the finite-support window; outside `b - a`, either
the source factor is zero below `a` or the target factor is zero above `b`. -/

/-- If `K` is supported in degrees at most `b` and `L` in degrees at least `a`, then
`Hom^•(K, L)` is supported in degrees at least `a - b`. -/
@[stacks 0A8H "lower support bound for a module-valued Hom complex"]
theorem isStrictlyGE {a b : ℤ} (hK : K.IsStrictlyLE b) (hL : L.IsStrictlyGE a) :
    (moduleComplex R K L).IsStrictlyGE (a - b) := sorry
/- Proof strategy: use the same degree-support decomposition with the reversed cutoff
`a - b`, invoking `degreeFamily_isZero_of_source` and `degreeFamily_isZero_of_target`
from `CochainComplex.HomComplex.FiniteWindow`. -/

/-- A Hom complex from a bounded-below complex to a bounded-above complex is bounded above. -/
@[stacks 0A8H "upper boundedness of a Hom complex"]
theorem minus
    (hK : CochainComplex.plus C K)
    (hL : CochainComplex.minus C L) :
    CochainComplex.minus (ModuleCat R) (moduleComplex R K L) := sorry
/- Proof strategy: unpack the two support witnesses and apply `isStrictlyLE` to obtain a
uniform upper cutoff for the Hom complex. -/

/-- A Hom complex from a bounded-above complex to a bounded-below complex is bounded below. -/
@[stacks 0A8H "lower boundedness of a Hom complex"]
theorem plus
    (hK : CochainComplex.minus C K)
    (hL : CochainComplex.plus C L) :
    CochainComplex.plus (ModuleCat R) (moduleComplex R K L) := sorry
/- Proof strategy: unpack the support witnesses and apply `isStrictlyGE` to obtain a
uniform lower cutoff for the Hom complex. -/

/-- The Hom complex between two bounded complexes is bounded. -/
@[stacks 0A8H "boundedness of a Hom complex"]
theorem bounded
    (hK : CochainComplex.bounded C K)
    (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded (ModuleCat R) (moduleComplex R K L) := sorry
/- Proof strategy: split `hK` and `hL` with `CochainComplex.bounded_iff`, then combine the upper
and lower support bounds and repackage them with the same characterization. -/

end CochainComplex.HomComplex
