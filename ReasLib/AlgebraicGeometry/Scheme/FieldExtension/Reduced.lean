/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over

/-!
# Reductions of field-extension base changes

This leaf owns the reduction of the canonical base change of a scheme over a
field.  It is independent of reducedness or finite-type hypotheses used by
applications.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Reduced

/-- The reduction of the field-extension base change of a scheme over `Spec k`,
viewed over `Spec K`. -/
abbrev baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) : Over (Spec (CommRingCat.of K)) :=
  Over.mk
    (Scheme.reductionι (FieldExtension.baseChange k K X.hom) ≫
      FieldExtension.toBase k K X.hom)

end FieldExtension.Reduced

end AlgebraicGeometry
