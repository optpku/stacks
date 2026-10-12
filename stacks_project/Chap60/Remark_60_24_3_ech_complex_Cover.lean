/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap60.Definition_60_9_1
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Crystalline

universe u

variable {A : Type u} [CommRing A]
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Canonical ring map `A → Γ(X, U)` from the structure map `X ⟶ Spec A`. -/
noncomputable def openSectionsRingHom (x₀ : X ⟶ I.subscheme) (U : X.Opens) :
    A →+* Γ(X, U) :=
  ((x₀ ≫ I.subschemeι).appLE ⊤ U le_top).hom.comp
    (Scheme.ΓSpecIso (.of A)).inv.hom

/-- Canonical `A`-algebra structure on sections of `X` over an open. -/
noncomputable abbrev openSectionsAlgebra (x₀ : X ⟶ I.subscheme) (U : X.Opens) :
    Algebra A Γ(X, U) :=
  (openSectionsRingHom x₀ U).toAlgebra

/-- The canonical algebra is induced by `openSectionsRingHom`. -/
theorem openSectionsAlgebra_eq (x₀ : X ⟶ I.subscheme) (U : X.Opens) :
    openSectionsAlgebra x₀ U = (openSectionsRingHom x₀ U).toAlgebra :=
  rfl

/-- The structure map on global sections is the named ring hom. -/
theorem openSectionsRingHom_eq (x₀ : X ⟶ I.subscheme) (U : X.Opens) :
    openSectionsRingHom x₀ U =
      ((x₀ ≫ I.subschemeι).appLE ⊤ U le_top).hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom :=
  rfl

/-- Affine open covering of a separated scheme over `Spec(A / I)` together with
polynomial presentations `P_idx → Γ(X, U_idx)` as in Remark 60.24.3. -/
structure CechCrisCover (x₀ : X ⟶ I.subscheme) where
  /-- Index set of the affine open covering. -/
  Λ : Type u
  /-- Affine open sets `U_idx`. -/
  U : Λ → X.affineOpens
  /-- The sets `U_idx` cover `X`. -/
  coversTop : ⨆ idx, (U idx).1 = ⊤
  /-- `X` is separated over the closed fibre `Spec(A / I)`. -/
  h_separated : IsSeparated x₀
  /-- Polynomial variable index types for each `P_idx`. -/
  vars : Λ → Type u
  /-- Surjective presentations `P_idx → Γ(X, U_idx)`. -/
  π : ∀ idx, MvPolynomial (vars idx) A →+* Γ(X, (U idx).1)
  /-- Each presentation is an `A`-algebra map. -/
  hπ_comp : ∀ idx,
    (π idx).comp (algebraMap A (MvPolynomial (vars idx) A)) =
      openSectionsRingHom x₀ (U idx).1
  /-- Each presentation is surjective. -/
  hπ : ∀ idx, Function.Surjective (π idx)

namespace CechCrisCover

variable (c : CechCrisCover x₀)

/-- Assemble a Čech crystalline covering from an affine open cover and polynomial
presentations. -/
def ofFamily
    (Λ : Type u) (U : Λ → X.affineOpens)
    (coversTop : ⨆ idx, (U idx).1 = ⊤) (h_separated : IsSeparated x₀)
    (vars : Λ → Type u)
    (π : ∀ idx, MvPolynomial (vars idx) A →+* Γ(X, (U idx).1))
    (hπ_comp : ∀ idx,
      (π idx).comp (algebraMap A (MvPolynomial (vars idx) A)) =
        openSectionsRingHom x₀ (U idx).1)
    (hπ : ∀ idx, Function.Surjective (π idx)) :
    CechCrisCover x₀ :=
  { Λ, U, coversTop, h_separated, vars, π, hπ_comp, hπ }

/-- Affine open corresponding to a finite tuple `σ = (idx_0,…,idx_n)`. -/
def simplexOpen (n : ℕ) (σ : Fin (n + 1) → c.Λ) : X.Opens :=
  ⨅ i, (c.U (σ i)).1

/-- Finite intersections of affine opens on a separated scheme remain affine. -/
theorem isAffineIntersection (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    IsAffineOpen (c.simplexOpen n σ) :=
  sorry

/-- The scheme of a simplex open is affine. -/
theorem isAffine_simplexScheme (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    IsAffine (c.simplexOpen n σ).toScheme :=
  sorry

/-- Affine scheme `U_{idx_0…idx_n}` of a simplex. -/
def simplexScheme (n : ℕ) (σ : Fin (n + 1) → c.Λ) : Scheme.{u} :=
  (c.simplexOpen n σ).toScheme

/-- Coordinate ring `C_{idx_0…idx_n} = Γ(U_{idx_0…idx_n})`. -/
abbrev simplexRing (n : ℕ) (σ : Fin (n + 1) → c.Λ) : Type u :=
  Γ(X, c.simplexOpen n σ)

/-- The simplex open is the infimum of the covering members. -/
theorem simplexOpen_eq (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    c.simplexOpen n σ = ⨅ i, (c.U (σ i)).1 :=
  rfl

/-- The simplex scheme is the open subscheme of the intersection. -/
theorem simplexScheme_eq (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    c.simplexScheme n σ = (c.simplexOpen n σ).toScheme :=
  rfl

/-- The simplex coordinate ring is global sections of the intersection. -/
theorem simplexRing_eq (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    c.simplexRing n σ = Γ(X, c.simplexOpen n σ) :=
  rfl

/-- A simplex open is contained in each of its covering members. -/
theorem simplexOpen_le_member (n : ℕ) (σ : Fin (n + 1) → c.Λ)
    (i : Fin (n + 1)) :
    c.simplexOpen n σ ≤ (c.U (σ i)).1 :=
  sorry

/-- The degree-zero simplex open is the corresponding covering member. -/
theorem simplexOpen_zero (σ : Fin 1 → c.Λ) :
    c.simplexOpen 0 σ = (c.U (σ 0)).1 :=
  sorry

/-- A successor simplex open is contained in the tail intersection. -/
theorem simplexOpen_succ_le (n : ℕ) (σ : Fin (n + 2) → c.Λ) :
    c.simplexOpen (n + 1) σ ≤ c.simplexOpen n (fun i => σ i.succ) :=
  sorry

/-- Restriction of sections along an inclusion of opens. -/
def restriction {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

/-- Applying restriction recovers the presheaf restriction map. -/
theorem restriction_apply {U V : X.Opens} (h : V ≤ U) :
    restriction h = (X.presheaf.map (homOfLE h).op).hom :=
  rfl

/-- Each covering member is affine, equivalently `U_idx = Spec Γ(X, U_idx)`. -/
theorem specIso (idx : c.Λ) :
    Nonempty ((c.U idx).1.toScheme ≅ Spec Γ(X, (c.U idx).1)) :=
  sorry

/-- The chosen affine opens cover `X`. -/
theorem coversTop_spec : ⨆ idx, (c.U idx).1 = ⊤ :=
  sorry

/-- The structure morphism `X ⟶ Spec(A / I)` is separated. -/
theorem isSeparated_spec : IsSeparated x₀ :=
  sorry

/-- Each chosen polynomial presentation is surjective. -/
theorem presentation_surjective (idx : c.Λ) :
    Function.Surjective (c.π idx) :=
  sorry

/-- Reindexing a simplex along a map of index tuples enlarges the intersection. -/
public theorem simplexOpen_reindex_le {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (σ : Fin (m + 1) → c.Λ) :
    c.simplexOpen m σ ≤ c.simplexOpen n (fun i => σ (f i)) :=
  sorry

/-- `I` dies on every simplex coordinate ring, since `X` lies over `Spec(A / I)`. -/
theorem simplex_hIC (IA : Ideal A) (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Ideal.map (openSectionsRingHom x₀ (c.simplexOpen n σ)) IA =
      (⊥ : Ideal (c.simplexRing n σ)) :=
  sorry

/-- `p` is nilpotent on each affine simplex coordinate ring. -/
theorem simplex_hpnil (p : ℕ) (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    IsNilpotent (p : c.simplexRing n σ) :=
  sorry

end CechCrisCover

end
