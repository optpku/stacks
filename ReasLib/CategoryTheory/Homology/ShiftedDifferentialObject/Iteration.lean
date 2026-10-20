module

public import ReasLib.CategoryTheory.Homology.ShiftedDifferentialObject

/-!
# Iterating a Unit-Shifted Differential

A differential `X ⟶ X⟦1⟧` determines a cochain complex whose degree-`n` object is `X⟦n⟧`.
This module owns that construction and its comparison with shifted homology.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

section ShiftedDifferentialObject

variable [Abelian A]

section ShiftFunctorPages

variable [HasShift A ℤ]

namespace ShiftedDifferentialObject

namespace Iteration

/-- For the unit shift `X ⟶ X⟦1⟧`, the induced differential on the `n`-th shifted component. -/
@[stacks 0AMI "unit-shift page differential"]
noncomputable def differential
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    X.obj⟦n⟧ ⟶ X.obj⟦n + 1⟧ :=
  (X.d⟦n⟧' : X.obj⟦n⟧ ⟶ (shiftFunctor A (1 : ℤ) ⋙ shiftFunctor A n).obj X.obj) ≫
    (shiftFunctorComm A (1 : ℤ) n).hom.app X.obj ≫
    (shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj

/-- Successive differentials in the canonical shifted page complex compose to zero. -/
theorem differential_sq
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    differential X n ≫ differential X (n + 1) = 0 := sorry
/-- The canonical cochain complex attached to a shifted differential object for the unit shift. -/
@[stacks 0AMI "unit-shift realization"]
noncomputable def complex
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) :
    CochainComplex A ℤ :=
  CochainComplex.of
    (fun n : ℤ ↦ X.obj⟦n⟧)
    (differential X)
    (differential_sq X)

/-- The object in degree `n` of the iterated shifted page complex is `X.obj⟦n⟧`. -/
@[simp]
theorem complex_X
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (complex X).X n = X.obj⟦n⟧ := sorry

/-- The inverse equivalence chosen by
`Iso.isoInverseOfIsoFunctor` is the natural isomorphism from `⟦-1⟧` to the abstract inverse
functor of `⟦1⟧`. -/
private noncomputable abbrev inverseNatIso :
    shiftFunctor A (-1 : ℤ) ≅ (shiftFunctor A (1 : ℤ)).inv :=
  Iso.isoInverseOfIsoFunctor
    (G := shiftEquiv A (1 : ℤ))
    (G' := (shiftFunctor A (1 : ℤ)).asEquivalence)
    (Iso.refl _)

/-- The chosen inverse to the unit shift is canonically
identified with the concrete `(-1)`-shift. -/
private noncomputable def inverseIso (X : A) :
    ((shiftFunctor A (-1 : ℤ)).obj X) ≅ ((shiftFunctor A (1 : ℤ)).inv.obj X) :=
  (inverseNatIso (A := A)).app X

/-- The first object of the shifted-page short complex is the
`n`-shift of the previous page. -/
private noncomputable abbrev firstObjectIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    X.obj⟦n - 1⟧ ≅ ((shiftFunctor A n).obj ((shiftFunctor A (1 : ℤ)).inv.obj X.obj)) :=
  shiftAdd X.obj n (-1 : ℤ) ≪≫
    shiftComm X.obj n (-1 : ℤ) ≪≫
      (shiftFunctor A n).mapIso (inverseIso (A := A) X.obj)

/-- The third object of the shifted page complex matches the
shifted target object of the associated short complex. -/
private noncomputable abbrev thirdObjectIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    X.obj⟦n + 1⟧ ≅ ((shiftFunctor A n).obj ((shiftFunctor A (1 : ℤ)).obj X.obj)) :=
  shiftAdd X.obj n (1 : ℤ) ≪≫ (shiftComm X.obj (1 : ℤ) n).symm

/-- The first square of the explicit `(n - 1, n, n + 1)` short
complex has the exact `ShortComplex.isoMk` shape. -/
private theorem shortComplexIso_comm₁₂_isoMk
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (firstObjectIso (A := A) X n).hom ≫
      (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).f) =
        ((complex X).sc' (n - 1) n (n + 1)).f ≫
          (Iso.refl (((complex X).sc' (n - 1) n (n + 1)).X₂)).hom := sorry
/-- The second square of the explicit `(n - 1, n, n + 1)` short
complex has the exact `ShortComplex.isoMk` shape. -/
private theorem shortComplexIso_comm₂₃_isoMk
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (Iso.refl (((complex X).sc' (n - 1) n (n + 1)).X₂)).hom ≫
        (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).g) =
      ((complex X).sc' (n - 1) n (n + 1)).g ≫
        (thirdObjectIso (A := A) X n).hom := sorry
/-- The shifted short complex of the iterated page complex is
canonically identified with the shifted short complex of the differential object. -/
@[no_expose]
noncomputable def shortComplexIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    ((complex X)⟦n⟧).sc (0 : ℤ) ≅
      ((shiftFunctor A n).mapShortComplex.obj X.shortComplex) :=
  -- Proof comment: first use the canonical shift/short-complex comparison to move from
  -- `((complex X)⟦n⟧).sc 0` to `(complex X).sc n`, then replace
  -- the two endpoint objects by the corresponding shifted page objects.
  (CochainComplex.shiftShortComplexFunctorIso A n (0 : ℤ) n (add_zero n)).app
      (complex X) ≪≫
    (complex X).isoSc' (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n) ≪≫
    ShortComplex.isoMk
      (firstObjectIso (A := A) X n)
      (Iso.refl _)
      (thirdObjectIso (A := A) X n)
      (shortComplexIso_comm₁₂_isoMk (A := A) X n)
      (shortComplexIso_comm₂₃_isoMk (A := A) X n)

/-- The `n`-th homology of the canonical shifted page complex is the `n`-fold shift of the
homology object of the shifted differential. -/
@[stacks 0AMI "unit-shift homology comparison"]
noncomputable def homologyIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (complex X).homology n ≅ X.homology⟦n⟧ :=
  (((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (0 : ℤ)).shiftIso
      n (0 : ℤ) n (add_zero n)).app (complex X)).symm ≪≫
    ShortComplex.homologyMapIso (shortComplexIso X n) ≪≫
      X.shortComplex.mapHomologyIso (shiftFunctor A n)

end Iteration

end ShiftedDifferentialObject

end ShiftFunctorPages

end ShiftedDifferentialObject

end CategoryTheory
