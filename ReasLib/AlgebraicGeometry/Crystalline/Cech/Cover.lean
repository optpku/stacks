/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Crystalline.Affine
public import Mathlib.Algebra.Category.CommAlgCat.Basic

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
polynomial presentations `P_idx → Γ(X, U_idx)`. -/
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

/-- The affine members cover the scheme, its structural map is separated, and the
polynomial presentations are surjective maps over the base ring. -/
theorem spec :
    (⨆ idx, (c.U idx).1 = ⊤) ∧ IsSeparated x₀ ∧
      (∀ idx, (c.π idx).comp (algebraMap A (MvPolynomial (c.vars idx) A)) =
        openSectionsRingHom x₀ (c.U idx).1) ∧
      (∀ idx, Function.Surjective (c.π idx)) :=
  ⟨c.coversTop, c.h_separated, c.hπ_comp, c.hπ⟩

/-- Scalar action on the sections of a covering member, induced by its structural map. -/
def memberAlgebra (idx : c.Λ) : Algebra A Γ(X, (c.U idx).1) :=
  openSectionsAlgebra x₀ (c.U idx).1

/-- The member scalar action is induced by the structural map on sections. -/
theorem memberAlgebra_eq (idx : c.Λ) :
    c.memberAlgebra idx = (openSectionsRingHom x₀ (c.U idx).1).toAlgebra := rfl

/-- Affine open corresponding to a finite tuple `σ = (idx_0,…,idx_n)`. -/
def simplexOpen (n : ℕ) (σ : Fin (n + 1) → c.Λ) : X.Opens :=
  ⨅ i, (c.U (σ i)).1

/-- Finite intersections of affine opens on a separated scheme remain affine. -/
theorem isAffineIntersection (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    IsAffineOpen (c.simplexOpen n σ) := by
  letI : IsSeparated x₀ := c.h_separated
  haveI : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (x₀ ≫ I.subschemeι)]
    infer_instance⟩
  exact IsAffineOpen.iInf (fun i => (c.U (σ i)).2)

/-- The scheme of a simplex open is affine. -/
theorem isAffine_simplexScheme (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    IsAffine (c.simplexOpen n σ).toScheme := c.isAffineIntersection n σ

/-- Affine scheme `U_{idx_0…idx_n}` of a simplex. -/
def simplexScheme (n : ℕ) (σ : Fin (n + 1) → c.Λ) : Scheme.{u} :=
  (c.simplexOpen n σ).toScheme

/-- The coordinate algebra of a finite affine intersection, with its structural scalar action. -/
def simplexAlgebra (n : ℕ) (σ : Fin (n + 1) → c.Λ) : CommAlgCat A :=
  @CommAlgCat.of A _ Γ(X, c.simplexOpen n σ) _
    (openSectionsAlgebra x₀ (c.simplexOpen n σ))

/-- Coordinate ring `C_{idx_0…idx_n} = Γ(U_{idx_0…idx_n})`. -/
abbrev simplexRing (n : ℕ) (σ : Fin (n + 1) → c.Λ) : Type u :=
  c.simplexAlgebra n σ

/-- Scalar action on a simplex coordinate ring, extracted from its canonical algebra bundle. -/
def simplexRing.algebra (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Algebra A (c.simplexRing n σ) := (c.simplexAlgebra n σ).algebra

/-- The simplex scalar action is induced by its structural map on sections. -/
theorem simplexRing.algebra_eq (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    simplexRing.algebra c n σ = (openSectionsRingHom x₀ (c.simplexOpen n σ)).toAlgebra := rfl

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
  iInf_le (fun j => (c.U (σ j)).1) i

/-- The degree-zero simplex open is the corresponding covering member. -/
theorem simplexOpen_zero (σ : Fin 1 → c.Λ) :
    c.simplexOpen 0 σ = (c.U (σ 0)).1 := by
  simp [simplexOpen]

/-- A successor simplex open is contained in the tail intersection. -/
theorem simplexOpen_succ_le (n : ℕ) (σ : Fin (n + 2) → c.Λ) :
    c.simplexOpen (n + 1) σ ≤ c.simplexOpen n (fun i => σ i.succ) :=
  le_iInf (fun i => c.simplexOpen_le_member (n + 1) σ i.succ)

/-- Restriction of sections along an inclusion of opens. -/
def restriction {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

/-- Applying restriction recovers the presheaf restriction map. -/
theorem restriction_apply {U V : X.Opens} (h : V ≤ U) :
    restriction h = (X.presheaf.map (homOfLE h).op).hom :=
  rfl

/-- Each covering member is affine, equivalently `U_idx = Spec Γ(X, U_idx)`. -/
def specIso (idx : c.Λ) :
    (c.U idx).1.toScheme ≅ Spec Γ(X, (c.U idx).1) :=
  (c.U idx).2.isoSpec

/-- The chosen affine opens cover `X`. -/
theorem coversTop_spec : ⨆ idx, (c.U idx).1 = ⊤ := c.coversTop

include c in
/-- The structure morphism `X ⟶ Spec(A / I)` is separated. -/
theorem isSeparated_spec : IsSeparated x₀ := c.h_separated

/-- Each chosen polynomial presentation is surjective. -/
theorem presentation_surjective (idx : c.Λ) :
    Function.Surjective (c.π idx) := c.hπ idx

/-- Reindexing a simplex along a map of index tuples enlarges the intersection. -/
public theorem simplexOpen_reindex_le {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (σ : Fin (m + 1) → c.Λ) :
    c.simplexOpen m σ ≤ c.simplexOpen n (fun i => σ (f i)) :=
  le_iInf (fun i => c.simplexOpen_le_member m σ (f i))

/-- `I` dies on every simplex coordinate ring, since `X` lies over `Spec(A / I)`. -/
theorem simplex_hIC (IA : Ideal A) (hI : Affine.idealCompatible IA I) (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Ideal.map (openSectionsRingHom x₀ (c.simplexOpen n σ)) IA =
      (⊥ : Ideal (c.simplexRing n σ)) := by
  refine (Ideal.map_eq_bot_iff_le_ker (I := IA)
    (openSectionsRingHom x₀ (c.simplexOpen n σ))).2 ?_
  intro a ha
  have htop : I.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom IA := by
    rw [hI, Scheme.IdealSheafData.ofIdealTop_ideal]
    simp
  have ha' : (Scheme.ΓSpecIso (.of A)).inv.hom a ∈
      RingHom.ker (I.subschemeι.app ⊤).hom := by
    rw [I.ker_subschemeι_app ⟨⊤, isAffineOpen_top _⟩, htop]
    change (Scheme.ΓSpecIso (.of A)).hom.hom
      ((Scheme.ΓSpecIso (.of A)).inv.hom a) ∈ IA
    simpa using ha
  change (I.subschemeι.app ⊤).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a) = 0 at ha'
  change ((x₀ ≫ I.subschemeι).appLE ⊤ _ le_top).hom
    ((Scheme.ΓSpecIso (.of A)).inv.hom a) = 0
  rw [Scheme.Hom.comp_appLE]
  exact (congrArg (x₀.appLE ⊤ (c.simplexOpen n σ) le_top).hom ha').trans (map_zero _)

/-- The open chart of a simplex intersection in `X`. -/
def simplexSpecι (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Spec (.of (c.simplexRing n σ)) ⟶ X :=
  (c.isAffineIntersection n σ).isoSpec.inv ≫ (c.simplexOpen n σ).ι

/-- Each simplex chart is an open immersion. -/
theorem simplexSpecι_open (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    IsOpenImmersion (c.simplexSpecι n σ) := by
  change IsOpenImmersion (c.isAffineIntersection n σ).fromSpec
  infer_instance

/-- The chart map uses the original `A`-algebra structure of its section ring. -/
theorem simplexSpecι_base (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    c.simplexSpecι n σ ≫ x₀ ≫ I.subschemeι =
      Spec.map (CommRingCat.ofHom (openSectionsRingHom x₀ (c.simplexOpen n σ))) := by
  change (c.isAffineIntersection n σ).fromSpec ≫ (x₀ ≫ I.subschemeι) = _
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec (x₀ ≫ I.subschemeι)
    (isAffineOpen_top _) (c.isAffineIntersection n σ) le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- `p` is nilpotent on each affine simplex coordinate ring. -/
theorem simplex_hpnil (p : ℕ) (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    IsNilpotent (p : c.simplexRing n σ) :=
  h_p ⟨c.simplexOpen n σ, c.isAffineIntersection n σ⟩

end CechCrisCover

end
