/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import stacks_project.Chap111.Exercise_111_66_7_Hyperelliptic

/-!
# Families of hyperelliptic curves and their naive number of moduli

This leaf owns the object and family predicates for smooth projective
hyperelliptic curves of a fixed genus, the `k`-point fibre of such a family,
and the covering-dimension count used as a naive number of moduli.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- A smooth projective hyperelliptic curve of genus `g` over the field `k`. -/
def IsHyperellipticCurveOfGenus {k : Type u} [Field k] (g : ℕ)
    (X : SchemeOverField k) : Prop :=
  ∃ (_ : Curve X) (_ : Smooth X.hom) (_ : Projective X.hom)
      (_ : GeometricallyIrreducible X.hom),
    IsHyperelliptic X ∧ genus X = g

/-- Unfold `IsHyperellipticCurveOfGenus g X` into the curve, smoothness, projectivity,
geometric irreducibility, hyperellipticity, and genus conditions. -/
theorem isHyperellipticCurveOfGenus_iff {k : Type u} [Field k] (g : ℕ)
    (X : SchemeOverField k) :
    IsHyperellipticCurveOfGenus g X ↔
      ∃ (_ : Curve X) (_ : Smooth X.hom) (_ : Projective X.hom)
          (_ : GeometricallyIrreducible X.hom),
        IsHyperelliptic X ∧ genus X = g :=
  sorry

/-- A family of hyperelliptic curves of genus `g` over a variety is a proper flat
morphism whose every scheme-theoretic fibre is a smooth projective hyperelliptic
curve of genus `g`. -/
def IsHyperellipticFamily {k : Type u} [Field k] {X V : SchemeOverField k}
    (g : ℕ) (f : X ⟶ V) : Prop :=
  Variety V ∧ IsProper f.left ∧ Flat f.left ∧
    ∀ y : V.left,
      IsHyperellipticCurveOfGenus g
        (Over.mk (f.left.fiberOverSpecResidueField y).hom)

/-- Unfold `IsHyperellipticFamily g f` into the variety, properness, flatness, and
fibrewise hyperelliptic-curve conditions. -/
theorem isHyperellipticFamily_iff {k : Type u} [Field k]
    {X V : SchemeOverField k} (g : ℕ) (f : X ⟶ V) :
    IsHyperellipticFamily g f ↔
      Variety V ∧ IsProper f.left ∧ Flat f.left ∧
        ∀ y : V.left,
          IsHyperellipticCurveOfGenus g
            (Over.mk (f.left.fiberOverSpecResidueField y).hom) :=
  sorry

/-- The fibre of a family of schemes over `k` at a `k`-rational point, as a scheme
over `k`. -/
noncomputable def familyFiber {k : Type u} [Field k] {X V : SchemeOverField k}
    (f : X ⟶ V) (v : 𝟙_ (SchemeOverField k) ⟶ V) : SchemeOverField k :=
  pullback f v

/-- `familyFiber f v` is the pullback of the family morphism along the `k`-point `v`. -/
theorem familyFiber_spec {k : Type u} [Field k] {X V : SchemeOverField k}
    (f : X ⟶ V) (v : 𝟙_ (SchemeOverField k) ⟶ V) :
    familyFiber f v = pullback f v :=
  sorry

/-- The naive moduli problem of smooth projective hyperelliptic curves of genus `g`
is covered in dimension `d` when finitely many hyperelliptic families of genus `g`,
with variety bases of dimension at most `d`, realize every such curve over `k` as a
`k`-point fibre up to isomorphism of `k`-schemes. -/
def IsHyperellipticModuliCoveredInDimension (k : Type u) [Field k] [IsAlgClosed k]
    (g d : ℕ) : Prop :=
  ∃ (n : ℕ) (X : Fin n → SchemeOverField k) (V : Fin n → SchemeOverField k)
    (f : (i : Fin n) → X i ⟶ V i),
    (∀ i, IsHyperellipticFamily g (f i)) ∧
      (∀ i, topologicalKrullDim (V i).left ≤ d) ∧
        ∀ C : SchemeOverField k, IsHyperellipticCurveOfGenus g C →
          ∃ (i : Fin n) (v : 𝟙_ (SchemeOverField k) ⟶ V i),
            Nonempty (C ≅ familyFiber (f i) v)

/-- Unfold covering in dimension `d` into a finite family of hyperelliptic families
of bounded base dimension that realize every object as a `k`-point fibre. -/
theorem isHyperellipticModuliCoveredInDimension_iff
    (k : Type u) [Field k] [IsAlgClosed k] (g d : ℕ) :
    IsHyperellipticModuliCoveredInDimension k g d ↔
      ∃ (n : ℕ) (X : Fin n → SchemeOverField k) (V : Fin n → SchemeOverField k)
        (f : (i : Fin n) → X i ⟶ V i),
        (∀ i, IsHyperellipticFamily g (f i)) ∧
          (∀ i, topologicalKrullDim (V i).left ≤ d) ∧
            ∀ C : SchemeOverField k, IsHyperellipticCurveOfGenus g C →
              ∃ (i : Fin n) (v : 𝟙_ (SchemeOverField k) ⟶ V i),
                Nonempty (C ≅ familyFiber (f i) v) :=
  sorry

/-- The naive number of moduli of smooth projective hyperelliptic curves of genus
`g` over an algebraically closed field `k`. -/
noncomputable def hyperellipticNumberOfModuli (k : Type u) [Field k] [IsAlgClosed k]
    (g : ℕ) : ℕ :=
  sInf {d | IsHyperellipticModuliCoveredInDimension k g d}

/-- For `2 ≤ g`, the naive number of moduli equals `2 * g - 1` if and only if the
problem is covered in dimension `2 * g - 1` and in no smaller dimension. -/
theorem hyperellipticNumberOfModuli_spec {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} (hg : 2 ≤ g) :
    hyperellipticNumberOfModuli k g = 2 * g - 1 ↔
      IsHyperellipticModuliCoveredInDimension k g (2 * g - 1) ∧
        ∀ d < 2 * g - 1, ¬ IsHyperellipticModuliCoveredInDimension k g d :=
  sorry

end AlgebraicGeometry.Curve
