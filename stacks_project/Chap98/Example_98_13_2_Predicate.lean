/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Coordinate algebra and the functor `F` for the Artin versality counterexample

For a field `k`, write `Λ = k[s, t]`. The predicate `HasF` records the algebraic
condition `F(A) = *`: finitely many elements `fi` together with the images of `s`
and `t` generate the unit ideal, and each `fi` is annihilated by `s`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

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

/-- The polynomial ring `k[s, t]` is Noetherian. -/
instance instIsNoetherianRing_coordRing (k : Type u) [Field k] :
    IsNoetherianRing (coordRing k) :=
  inferInstance

/-- The ring homomorphism `R → A` associated to a morphism `Spec A ⟶ Spec R`. -/
def algebraMapOfHom {R A : CommRingCat} (f : Spec A ⟶ Spec R) : R →+* A :=
  CommRingCat.Hom.hom ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ (Scheme.ΓSpecIso A).hom)

/-- `algebraMapOfHom` is the composite of `ΓSpecIso` with global sections of `f`. -/
theorem algebraMapOfHom_spec {R A : CommRingCat} (f : Spec A ⟶ Spec R) :
    algebraMapOfHom f =
      CommRingCat.Hom.hom
        ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ (Scheme.ΓSpecIso A).hom) :=
  sorry

/-- The global section of `Spec A` corresponding to an element of `A`. -/
def globalSection {A : Type u} [CommRing A] (a : A) :
    Γ(Spec (CommRingCat.of A), ⊤) :=
  CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv a

/-- Restriction of a global section of `Spec A` to an open `W`. -/
def restrictSection {A : Type u} [CommRing A] (W : (Spec (CommRingCat.of A)).Opens)
    (a : Γ(Spec (CommRingCat.of A), ⊤)) : Γ(Spec (CommRingCat.of A), W) :=
  ((Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom a

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
  sorry

/-- The geometric condition that `V(s, t) ⊆ Spec(A)` has a quasi-compact open
neighbourhood on which `s` vanishes. -/
def ExistsQcOpen {k A : Type u} [Field k] [CommRing A] (φ : coordRing k →+* A) : Prop :=
  ∃ W : (Spec (CommRingCat.of A)).Opens,
    IsCompact (W : Set (Spec (CommRingCat.of A))) ∧
      (Spec (CommRingCat.of A)).zeroLocus
          ({globalSection (φ (s k)), globalSection (φ (t k))} :
            Set Γ(Spec (CommRingCat.of A), ⊤)) ⊆ W ∧
        restrictSection W (globalSection (φ (s k))) = 0

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

/-- The origin is the image of the closed point of `Spec(k)` under `originHom`. -/
theorem origin_eq (k : Type u) [Field k] :
    origin k = originHom k (IsLocalRing.closedPoint k) :=
  sorry

end AlgebraicGeometry.ArtinVersalityCounterexample
