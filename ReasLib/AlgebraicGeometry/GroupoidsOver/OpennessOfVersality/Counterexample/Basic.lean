/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point

/-!
# A covering condition defined by annihilators in a polynomial algebra

The finite generator condition on a two-variable polynomial algebra has a
quasi-compact neighbourhood interpretation and defines a full groupoid subfibration.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ArtinVersalityCounterexample

/-- The coordinate ring `Λ = k[s, t]`. -/
abbrev coordRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k

/-- The generator `s = X 0` of `coordRing k`. -/
def s (k : Type u) [Field k] : coordRing k :=
  MvPolynomial.X 0

/-- The generator `t = X 1` of `coordRing k`. -/
def t (k : Type u) [Field k] : coordRing k :=
  MvPolynomial.X 1

/-- The base scheme `Spec(Λ)`. -/
abbrev baseScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (coordRing k))

/-- The algebraic condition `F(A) = *`: the images of `s` and `t` together with
finitely many elements annihilated by `s` generate the unit ideal. -/
def HasF {k A : Type u} [Field k] [CommRing A] (φ : coordRing k →+* A) : Prop :=
  ∃ n : ℕ, ∃ f : Fin n → A,
    Ideal.span ({φ (s k), φ (t k)} ∪ Set.range f) = ⊤ ∧
      ∀ i : Fin n, f i * φ (s k) = 0

/-- `HasF φ` is the generator/annihilator condition on the `Λ`-algebra `φ`. -/
theorem hasF_spec {k A : Type u} [Field k] [CommRing A] (φ : coordRing k →+* A) :
    HasF φ ↔
      ∃ n : ℕ, ∃ f : Fin n → A,
        Ideal.span ({φ (s k), φ (t k)} ∪ Set.range f) = ⊤ ∧
          ∀ i : Fin n, f i * φ (s k) = 0 :=
  Iff.rfl

/-- The geometric condition that `V(s, t) ⊆ Spec(A)` has a quasi-compact open
neighbourhood on which `s` vanishes. -/
def ExistsQcOpen {k A : Type u} [Field k] [CommRing A] (φ : coordRing k →+* A) : Prop :=
  ∃ W : (Spec (CommRingCat.of A)).Opens,
    IsCompact (W : Set (Spec (CommRingCat.of A))) ∧
      (Spec (CommRingCat.of A)).zeroLocus
          ({(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (φ (s k)), (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (φ (t k))} :
            Set Γ(Spec (CommRingCat.of A), ⊤)) ⊆ W ∧
        (((Spec (CommRingCat.of A)).presheaf.map
          (homOfLE (le_top : W ≤ ⊤)).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (φ (s k)))) = 0

/-- Geometrically, `HasF φ` means there is a quasi-compact open neighbourhood of
`V(s, t) ⊆ Spec(A)` on which `s` vanishes. -/
theorem exists_qcOpen_iff {k A : Type u} [Field k] [CommRing A] (φ : coordRing k →+* A) :
    HasF φ ↔ ExistsQcOpen φ :=
  sorry

/-- The homomorphism `coordRing k → k` sending both `s` and `t` to `0`. -/
def originEval (k : Type u) [Field k] : coordRing k →+* k :=
  MvPolynomial.eval fun _ : Fin 2 ↦ (0 : k)

/-- The coordinate ring of `U = Spec(k[s, t] / (s))`. -/
abbrev testRing (k : Type u) [Field k] : Type u :=
  coordRing k ⧸ Ideal.span ({s k} : Set (coordRing k))

/-- The kernel of `originEval` contains the principal ideal `(s)`. -/
theorem originEval_eq_zero_of_mem_span_s {k : Type u} [Field k] {x : coordRing k}
    (hx : x ∈ Ideal.span ({s k} : Set (coordRing k))) :
    originEval k x = 0 :=
  sorry

/-- The residue map `k[s, t] / (s) → k` sending `t` to `0`. -/
def originRingHom (k : Type u) [Field k] : testRing k →+* k :=
  Ideal.Quotient.lift (Ideal.span ({s k} : Set (coordRing k))) (originEval k)
    fun _ ha ↦ originEval_eq_zero_of_mem_span_s ha

/-- The test scheme `U = Spec(k[s, t] / (s))`. -/
def testScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (testRing k))

/-- The structure morphism `U ⟶ Spec(Λ)` induced by the quotient `Λ → Λ / (s)`. -/
def testToBase (k : Type u) [Field k] : testScheme k ⟶ baseScheme k :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span ({s k} : Set (coordRing k)))))

/-- `U` as an object of `Over (Spec(Λ))`. -/
def testOver (k : Type u) [Field k] : Over (baseScheme k) :=
  Over.mk (testToBase k)

/-- The morphism `Spec(k) ⟶ U` cutting out the origin `(s, t)`. -/
def originHom (k : Type u) [Field k] : Spec (CommRingCat.of k) ⟶ testScheme k :=
  Spec.map (CommRingCat.ofHom (originRingHom k))

/-- The finite type point `u0 = (s, t)` of `U`. -/
def origin (k : Type u) [Field k] : testScheme k :=
  originHom k (IsLocalRing.closedPoint k)

variable (k : Type u) [Field k]

/-- A scheme over `Spec(Λ)` is covered when it has an affine open cover on which
`HasF` holds. -/
def IsCovered : ObjectProperty (Over (baseScheme k)) :=
  fun T ↦ ∃ 𝒰 : T.left.AffineOpenCover.{u},
    ∀ j : 𝒰.I₀, HasF ((AlgebraicGeometry.Spec.preimage (𝒰.f j ≫ T.hom)).hom)

/-- Membership in `IsCovered` is the existence of an affine open cover whose
coordinate rings satisfy `HasF`. -/
theorem isCovered_iff (T : Over (baseScheme k)) :
    IsCovered k T ↔
      ∃ 𝒰 : T.left.AffineOpenCover.{u},
        ∀ j : 𝒰.I₀, HasF ((AlgebraicGeometry.Spec.preimage (𝒰.f j ≫ T.hom)).hom) :=
  Iff.rfl

/-- The inclusion of schemes covered by `HasF` is fibred in groupoids over
`Over (Spec(Λ))`. -/
instance instIsFiberedInGroupoids_covered :
    Functor.IsFibered.InGroupoids (ObjectProperty.ι (IsCovered k)) :=
  sorry

/-- The category fibred in groupoids `X` of schemes over `Spec(Λ)` that admit an
affine open cover on which `HasF` holds. -/
def groupoids : GroupoidsOver (baseScheme k) :=
  FiberedCategoryOver.Groupoids.ofFunctor (ObjectProperty.ι (IsCovered k))

/-- The projection of `groupoids k` is the full-subcategory inclusion of
`IsCovered`. -/
theorem groupoids_p :
    (groupoids k).p = ObjectProperty.ι (IsCovered k) :=
  rfl

/-- The structure morphism `U ⟶ Spec(Λ)` is locally of finite type. -/
instance instLocallyOfFiniteType_testToBase : LocallyOfFiniteType (testToBase k) :=
  sorry

end AlgebraicGeometry.ArtinVersalityCounterexample
