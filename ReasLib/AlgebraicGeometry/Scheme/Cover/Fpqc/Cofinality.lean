module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Family

/-!
# Cofinality of fpqc covers

Fpqc covers of the spectrum of a nontrivial commutative ring do not admit a
small cofinal family under refinement.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace AlgebraicGeometry.FpqcCover

/-- No family indexed by a type in `Type v` is cofinal under refinement among
fpqc covers of the spectrum of a nontrivial commutative ring whose index types
lie in `Type (max u v + 1)`. -/
theorem not_exists_smallCofinalFamily_of_spec (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ ∃ (α : Type v)
        (A : α → FpqcCover.{u, max u v + 1}
          (Scheme.Spec.obj (Opposite.op (CommRingCat.of R)))),
      ∀ 𝒰 : FpqcCover.{u, max u v + 1}
          (Scheme.Spec.obj (Opposite.op (CommRingCat.of R))),
        ∃ a : α, Refines (A a).toOverFamily 𝒰.toOverFamily := sorry

end AlgebraicGeometry.FpqcCover
