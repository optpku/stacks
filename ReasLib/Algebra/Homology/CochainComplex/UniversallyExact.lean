module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Range

@[expose] public section

open CategoryTheory LinearMap

universe u v

variable {R : Type u} [CommRing R]

namespace HomologicalComplex

/-- The inclusion of cycles followed by the induced map to the next cycle object is zero. -/
theorem iCycles_toCycles (C : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    C.iCycles i ≫ C.toCycles i (i + 1) = 0 := sorry

/-- The canonical short complex `cycles i ⟶ C.X i ⟶ cycles (i + 1)` associated to an
integer-indexed cochain complex of modules. -/
noncomputable def cyclesShortComplex
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (C.iCycles i) (C.toCycles i (i + 1)) (C.iCycles_toCycles i)

/-- A cochain complex that remains exact after every tensor test decomposes degreewise into
universally exact short complexes of consecutive cycle objects. -/
theorem universallyExact_cyclesShortComplex
    (C : CochainComplex (ModuleCat.{v} R) ℤ)
    (hC : ∀ (i : ℤ) (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : Module R Q),
      range (rTensor Q (C.sc i).f.hom) =
        ker (rTensor Q (C.sc i).g.hom)) :
    ∀ i, (C.cyclesShortComplex i).UniversallyExact := sorry

end HomologicalComplex
