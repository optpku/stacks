module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth.Stratification

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.25.11: a finite-type scheme over a field admits, after a finite purely inseparable
extension and reduction, a finite descending filtration by closed subschemes whose successive
locally closed strata are smooth over the extended field. -/
@[stacks 0H3W]
#check (AlgebraicGeometry.SchemeOverField.exists_smoothStratification :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X],
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
      let Y := FieldExtension.Reduced.baseChange k k' X
      ∃ t : ℕ, ∃ Z : Fin (t + 1) → Y.left.IdealSheafData,
        Z 0 = ⊥ ∧
        Z (Fin.last t) = ⊤ ∧
        (∀ i : Fin t, Z i.castSucc ≤ Z i.succ) ∧
        ∀ i : Fin t,
          Smooth
            (((Z i.succ).comap (Z i.castSucc).subschemeι).openComplement.ι ≫
              (Z i.castSucc).subschemeι ≫ Y.hom))
