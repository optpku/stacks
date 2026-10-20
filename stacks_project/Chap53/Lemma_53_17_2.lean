/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.PicardTorsion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 53.17.2 (1) -/
@[stacks 0CDU] #check
  (AlgebraicGeometry.Curve.existsPicardTorsionGenusOne :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    [Smooth X.hom] (n g : ℕ) (h_n_pos : 1 ≤ n)
    (h_unit : IsUnit (n : k))
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : g = SchemeOverField.genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ)
    (h_g : g = 1),
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      ∃ x : SchemeOverField.point k' ⟶ FieldExtension.Over.baseChange k k' X,
        Nonempty
          (AddSubgroup.torsionBy
            (FieldExtension.Over.baseChange k k' X).left.PicardGroup (n : ℤ) ≃+
            (Fin 2 → ZMod n)))

/- Lemma 53.17.2 (2) -/
@[stacks 0CDU] #check
  (AlgebraicGeometry.Curve.existsPicardTorsionGenusGeTwo :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    [Smooth X.hom] (n g : ℕ) (h_n_pos : 1 ≤ n)
    (h_unit : IsUnit (n : k))
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : g = SchemeOverField.genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ)
    (h_g : 2 ≤ g),
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      ∃ x : SchemeOverField.point k' ⟶ FieldExtension.Over.baseChange k k' X,
        Module.finrank k k' ≤ (2 * g - 2) * Nat.factorial (n ^ (2 * g)) ∧
        Nonempty
          (AddSubgroup.torsionBy
            (FieldExtension.Over.baseChange k k' X).left.PicardGroup (n : ℤ) ≃+
            (Fin (2 * g) → ZMod n)))
