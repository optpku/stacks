/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.NatIso
public import stacks_project.Chap97.«97_13_0_1»
public import stacks_project.Chap97.Lemma_97_13_1_FixOne
public import stacks_project.Chap97.Lemma_97_13_1_Action

/-!
# The functor FA d is the action groupoid of G on X

The functor in groupoids `FA d` is isomorphic to the functor sending a scheme `T`
to the action groupoid of the unit-fixing subgroup `G(T)` on the `T`-points of
the universal free-algebra scheme.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FA

/-- Lemma 97.13.1: the functor in groupoids `FA d` is isomorphic to the functor
sending a scheme `T` to the action groupoid of `glFixOne Γ(T, ⊤) d` on
`FreeDimAlgebra Γ(T, ⊤) d`. Equivalently, the fibre over `T` has objects `X(T)`,
morphisms `G(T) × X(T)`, source the projection, target the conjugate right action
`conjugate g m`, and composition `((g, m), (g', m')) ↦ (g' * g, m')`.
Local erratum: the source formula is a right action under ordinary matrix
multiplication. The opposite-group ActionCategory realizes that formula; the
source's displayed `g * g'` must therefore be reversed in these coordinates. -/
@[stacks 05YP]
def isoActionGroupoid (d : ℕ) [NeZero d] : FA d ≅ actionGroupoid d :=
  NatIso.ofComponents (fun T ↦ fibreIso d T) sorry

/-- The forward component of `isoActionGroupoid` at `T` is `fibreIso`. -/
theorem isoActionGroupoid_hom_app (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (isoActionGroupoid d).hom.app T = (fibreIso d T).hom :=
  sorry

/-- The inverse component of `isoActionGroupoid` at `T` is the inverse of `fibreIso`. -/
theorem isoActionGroupoid_inv_app (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (isoActionGroupoid d).inv.app T = (fibreIso d T).inv :=
  sorry

/-- Objects of the fibre over `T` are the `T`-points of `baseScheme`. -/
def isoActionGroupoid_objects (d : ℕ) [NeZero d] (T : Scheme) :
    (T ⟶ UniversalFiniteFreeAlgebra.baseScheme ⟨d, Nat.pos_of_neZero d⟩) ≃
      FreeDimAlgebra Γ(T, ⊤) d :=
  UniversalFiniteFreeAlgebra.schemeHomEquiv T ⟨d, Nat.pos_of_neZero d⟩

/-- `isoActionGroupoid_objects` is the identification `schemeHomEquiv`. -/
theorem isoActionGroupoid_objects_apply (d : ℕ) [NeZero d] (T : Scheme)
    (f : T ⟶ UniversalFiniteFreeAlgebra.baseScheme ⟨d, Nat.pos_of_neZero d⟩) :
    isoActionGroupoid_objects d T f =
      UniversalFiniteFreeAlgebra.schemeHomEquiv T ⟨d, Nat.pos_of_neZero d⟩ f :=
  sorry

/-- Morphisms of the fibre over `T` correspond to pairs in `G(T) × X(T)`. -/
def isoActionGroupoid_arrows (d : ℕ) [NeZero d] (T : Scheme) :
    glFixOne Γ(T, ⊤) d ×
        (T ⟶ UniversalFiniteFreeAlgebra.baseScheme ⟨d, Nat.pos_of_neZero d⟩) ≃
      (Σ m : FreeDimAlgebra Γ(T, ⊤) d, Σ m' : FreeDimAlgebra Γ(T, ⊤) d, m ⟶ m') :=
  (Equiv.prodCongr (Equiv.refl _)
      (UniversalFiniteFreeAlgebra.schemeHomEquiv T ⟨d, Nat.pos_of_neZero d⟩)).trans
    (arrowEquiv Γ(T, ⊤) d)

/-- The `G(T)`-component of `isoActionGroupoid_arrows` is the identity on `glFixOne`. -/
theorem isoActionGroupoid_arrows_fst (d : ℕ) [NeZero d] (T : Scheme)
    (g : glFixOne Γ(T, ⊤) d)
    (f : T ⟶ UniversalFiniteFreeAlgebra.baseScheme ⟨d, Nat.pos_of_neZero d⟩) :
    ((isoActionGroupoid_arrows d T).symm
        (arrowEquiv Γ(T, ⊤) d (g, isoActionGroupoid_objects d T f))).1 = g :=
  sorry

/-- The source map on `G × X` is projection onto the algebra. -/
theorem isoActionGroupoid_source {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    (arrowEquiv R d (g, m)).1 = m :=
  sorry

/-- The target map on `G × X` is the right-conjugation formula `a(g, m) = conjugate g m`. -/
theorem isoActionGroupoid_target {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    (arrowEquiv R d (g, m)).2.1 = FreeDimAlgebra.conjugate g m :=
  sorry

/-- Composition in the source's matrix coordinates uses the right-action order:
if `m = conjugate g' m'`, the composite is `(g' * g, m')`. -/
theorem isoActionGroupoid_comp {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    {m₁ m₂ m₃ : FreeDimAlgebra R d} (φ : m₁ ⟶ m₂) (ψ : m₂ ⟶ m₃) :
    (homEquiv m₁ m₃ (φ ≫ ψ)).val =
      (homEquiv m₁ m₂ φ).val * (homEquiv m₂ m₃ ψ).val :=
  sorry

end AlgebraicGeometry.FA
