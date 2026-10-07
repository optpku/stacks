module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal

/-!
# Formal objects of a category over `C_Λ`

A formal object of `p : F ⥤ ArtinianLocalAlgCat Λ k` is a complete local base `R`
together with a sequential inverse system in `F` lying over the maximal-adic
truncations of `R`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v

noncomputable section

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/-- A formal object of `p` is a complete local algebra `R` with residue field `k`, together
with a sequential inverse system in `F` lying over the truncations `R ⧸ m_R^{n+1}`. -/
structure FormalObject (p : F ⥤ ArtinianLocalAlgCat Λ k) where
  /-- Complete local base of the formal object. -/
  base : CompleteLocalAlgCat Λ k
  /-- Inverse system of objects of `F` over the truncations of `base`. -/
  system : SequentialInverseSystem F
  /-- Stage `n` of the system lies over the `n`th truncation of `base`. -/
  over_obj : ∀ n : ℕ, p.obj (system.family n) = base.truncation n
  /-- The successor transition lies over the truncation projection of `base`. -/
  over_step : ∀ n : ℕ, p.IsHomLift (base.truncationMap n) (system.stepMap n)

namespace FormalObject

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- Package a complete local base and a compatible inverse system as a formal object. -/
noncomputable def of (R : CompleteLocalAlgCat Λ k) (ξ : ℕ → F)
    (f : ∀ n, ξ (n + 1) ⟶ ξ n)
    (over_obj : ∀ n, p.obj (ξ n) = R.truncation n)
    (over_step : ∀ n, p.IsHomLift (R.truncationMap n) (f n)) :
    FormalObject p where
  base := R
  system := Functor.ofOpSequence f
  over_obj := over_obj
  over_step := sorry

/-- The complete local base of a packaged formal object is the supplied algebra. -/
theorem of_base (R : CompleteLocalAlgCat Λ k) (ξ : ℕ → F) (f : ∀ n, ξ (n + 1) ⟶ ξ n)
    (over_obj : ∀ n, p.obj (ξ n) = R.truncation n)
    (over_step : ∀ n, p.IsHomLift (R.truncationMap n) (f n)) :
    (of R ξ f over_obj over_step).base = R := sorry

/-- Projection of a formal object to its complete local base. -/
def projection (ξ : FormalObject p) : CompleteLocalAlgCat Λ k :=
  ξ.base

/-- The projection of a formal object is its stored complete local base. -/
theorem projection_eq (ξ : FormalObject p) : ξ.projection = ξ.base := sorry

/-- Stagewise specification of a formal object over the truncations of its base. -/
theorem spec (ξ : FormalObject p) (n : ℕ) :
    p.obj (ξ.system.family n) = ξ.base.truncation n ∧
      p.IsHomLift (ξ.base.truncationMap n) (ξ.system.stepMap n) := sorry

/-- A morphism of formal objects is a complete local base map together with a natural
family of morphisms of `F` lying over the induced truncations. -/
structure Hom (ξ η : FormalObject p) where
  /-- Underlying morphism of complete local bases. -/
  base : ξ.base ⟶ η.base
  /-- Stagewise morphisms of the inverse systems. -/
  app : ∀ n : ℕ, ξ.system.family n ⟶ η.system.family n
  /-- Truncations of the base morphism, as morphisms in `ArtinianLocalAlgCat`. -/
  baseTrunc : ∀ n : ℕ, ξ.base.truncation n ⟶ η.base.truncation n
  /-- Each stage of `app` lies over the corresponding truncated base map. -/
  over : ∀ n : ℕ, p.IsHomLift (baseTrunc n) (app n)
  /-- The truncated base maps are the maximal-adic quotients of `base`. -/
  baseTrunc_spec : ∀ n : ℕ,
    (baseTrunc n).hom.toRingHom.comp (Ideal.Quotient.mk (maximalIdeal ξ.base.carrier ^ (n + 1))) =
      (Ideal.Quotient.mk (maximalIdeal η.base.carrier ^ (n + 1))).comp base.hom.toRingHom
  /-- The stagewise maps intertwine successor transitions. -/
  naturality : ∀ n : ℕ, ξ.system.stepMap n ≫ app n = app (n + 1) ≫ η.system.stepMap n

/-- Identity morphism of a formal object. -/
def Hom.id (ξ : FormalObject p) : Hom ξ ξ where
  base := 𝟙 ξ.base
  app := fun n ↦ 𝟙 (ξ.system.family n)
  baseTrunc := fun n ↦ 𝟙 (ξ.base.truncation n)
  over := sorry
  baseTrunc_spec := sorry
  naturality := sorry

/-- Composition of morphisms of formal objects. -/
def Hom.comp {ξ η ζ : FormalObject p} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ where
  base := a.base ≫ b.base
  app := fun n ↦ a.app n ≫ b.app n
  baseTrunc := fun n ↦ a.baseTrunc n ≫ b.baseTrunc n
  over := sorry
  baseTrunc_spec := sorry
  naturality := sorry

/-- A morphism of formal objects lies over its truncated base maps and commutes with
successor transitions. -/
theorem Hom.spec {ξ η : FormalObject p} (a : Hom ξ η) (n : ℕ) :
    p.IsHomLift (a.baseTrunc n) (a.app n) ∧
      ξ.system.stepMap n ≫ a.app n = a.app (n + 1) ≫ η.system.stepMap n := sorry

/-- The identity morphism has identity base map. -/
theorem Hom.id_base (ξ : FormalObject p) : (Hom.id ξ).base = 𝟙 ξ.base := sorry

/-- The identity morphism has identity stage maps. -/
theorem Hom.id_app (ξ : FormalObject p) (n : ℕ) :
    (Hom.id ξ).app n = 𝟙 (ξ.system.family n) := sorry

/-- Composition of formal morphisms composes base maps. -/
theorem Hom.comp_base {ξ η ζ : FormalObject p} (a : Hom ξ η) (b : Hom η ζ) :
    (Hom.comp a b).base = a.base ≫ b.base := sorry

/-- Composition of formal morphisms composes stage maps. -/
theorem Hom.comp_app {ξ η ζ : FormalObject p} (a : Hom ξ η) (b : Hom η ζ) (n : ℕ) :
    (Hom.comp a b).app n = a.app n ≫ b.app n := sorry

/-- Category of formal objects of `p`. -/
instance category : Category.{max u v} (FormalObject p) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end FormalObject

end
