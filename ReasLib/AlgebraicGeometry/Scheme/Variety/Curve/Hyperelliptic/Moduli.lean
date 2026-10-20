module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Hyperelliptic

/-!
# Moduli of hyperelliptic curves

This leaf defines the fixed-genus hyperelliptic-curve family and covering predicates
used to express the number of moduli.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Curve.Hyperelliptic.Moduli

/-- A smooth projective hyperelliptic curve of genus `g` over the field `k`. -/
def IsCurveOfGenus {k : Type u} [Field k] (g : ℕ) (X : SchemeOverField k) : Prop :=
  ∃ (_ : Curve X) (_ : Smooth X.hom) (_ : Projective X.hom)
      (_ : GeometricallyIrreducible X.hom),
    IsHyperelliptic X ∧ genus X = g

/-- The defining conditions for a smooth projective hyperelliptic curve of genus `g`. -/
theorem isCurveOfGenus_iff {k : Type u} [Field k] (g : ℕ) (X : SchemeOverField k) :
    IsCurveOfGenus g X ↔
      ∃ (_ : Curve X) (_ : Smooth X.hom) (_ : Projective X.hom)
          (_ : GeometricallyIrreducible X.hom),
        IsHyperelliptic X ∧ genus X = g := sorry

/-- A proper flat family of hyperelliptic curves of genus `g` over a variety. -/
def IsFamily {k : Type u} [Field k] {X V : SchemeOverField k}
    (g : ℕ) (f : X ⟶ V) : Prop :=
  Variety V ∧ IsProper f.left ∧ Flat f.left ∧
    ∀ y : V.left,
      IsCurveOfGenus g (Over.mk (f.left.fiberOverSpecResidueField y).hom)

/-- The defining conditions for a proper flat family of fixed-genus hyperelliptic curves. -/
theorem isFamily_iff {k : Type u} [Field k] {X V : SchemeOverField k}
    (g : ℕ) (f : X ⟶ V) :
    IsFamily g f ↔
      Variety V ∧ IsProper f.left ∧ Flat f.left ∧
        ∀ y : V.left,
          IsCurveOfGenus g (Over.mk (f.left.fiberOverSpecResidueField y).hom) := sorry

/-- A finite collection of families covers all genus-`g` hyperelliptic curves in dimension `d`. -/
def AdmitsCovering (k : Type u) [Field k] [IsAlgClosed k] (g d : ℕ) : Prop :=
  ∃ (n : ℕ) (X : Fin n → SchemeOverField k) (V : Fin n → SchemeOverField k)
    (f : (i : Fin n) → X i ⟶ V i),
    0 < n ∧
      (∀ i, IsFamily g (f i)) ∧
        (∀ i, topologicalKrullDim (V i).left ≤ d) ∧
          (∃ i, topologicalKrullDim (V i).left = d) ∧
            ∀ C : SchemeOverField k, IsCurveOfGenus g C →
              ∃ (i : Fin n) (v : 𝟙_ (SchemeOverField k) ⟶ V i),
                Nonempty (C ≅ pullback (f i) v)

/-- The finite-family, dimension, and fibre-isomorphism conditions for a covering. -/
theorem admitsCovering_iff (k : Type u) [Field k] [IsAlgClosed k] (g d : ℕ) :
    AdmitsCovering k g d ↔
      ∃ (n : ℕ) (X : Fin n → SchemeOverField k) (V : Fin n → SchemeOverField k)
        (f : (i : Fin n) → X i ⟶ V i),
        0 < n ∧
          (∀ i, IsFamily g (f i)) ∧
            (∀ i, topologicalKrullDim (V i).left ≤ d) ∧
              (∃ i, topologicalKrullDim (V i).left = d) ∧
                ∀ C : SchemeOverField k, IsCurveOfGenus g C →
                  ∃ (i : Fin n) (v : 𝟙_ (SchemeOverField k) ⟶ V i),
                    Nonempty (C ≅ pullback (f i) v) := sorry

/-- The number of moduli is `d` when a covering exists in dimension `d` and none exists below it. -/
def HasNumberOfModuli (k : Type u) [Field k] [IsAlgClosed k] (g d : ℕ) : Prop :=
  AdmitsCovering k g d ∧ ∀ e < d, ¬ AdmitsCovering k g e

/-- The defining attained-minimum condition for the number of moduli. -/
theorem hasNumberOfModuli_iff (k : Type u) [Field k] [IsAlgClosed k] (g d : ℕ) :
    HasNumberOfModuli k g d ↔
      AdmitsCovering k g d ∧ ∀ e < d, ¬ AdmitsCovering k g e := sorry

/-- Hyperelliptic curves of genus `g` have number of moduli `2 * g - 1` for `2 ≤ g`. -/
theorem hasNumberOfModuli_hyperelliptic {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} (hg : 2 ≤ g) :
    HasNumberOfModuli k g (2 * g - 1) := sorry

end AlgebraicGeometry.Curve.Hyperelliptic.Moduli
