module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_7_3

/-!
# Yoneda evaluation of restricted coyoneda morphisms

A based morphism from the category of elements of `restrictedCoyoneda R` to a
category cofibered in groupoids over `C_Λ` is evaluated on the identity
truncations of `R` to produce a formal object in the completion fibre over `R`.
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

open CompleteLocalAlgCat

noncomputable section

/-- Morphisms over `C_Λ` from the cofibered set associated to `restrictedCoyoneda R`
(the restriction `underline R |_{C_Λ}`) to a category `p` over `C_Λ`. -/
abbrev RestrictedHom (p : F ⥤ ArtinianLocalAlgCat Λ k) (R : CompleteLocalAlgCat Λ k) :=
  BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)) ⥤ᵇ
    BasedCategory.ofFunctor p

/-- `RestrictedHom p R` is the category of based functors from the category of
elements of `restrictedCoyoneda R` to `p`. -/
theorem RestrictedHom_eq (p : F ⥤ ArtinianLocalAlgCat Λ k) (R : CompleteLocalAlgCat Λ k) :
    RestrictedHom p R =
      (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)) ⥤ᵇ
        BasedCategory.ofFunctor p) := sorry

/-- The identity truncation `R ⟶ R ⧸ m_R^{n+1}` as an object of the category of
elements of `restrictedCoyoneda R`. -/
noncomputable def restrictedIdentity (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedCoyoneda R).Elements :=
  ⟨R.truncation n,
    { hom := Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1))
      isLocalHom := sorry
      residue_compat := sorry }⟩

/-- The base of `restrictedIdentity R n` is the `n`th truncation of `R`. -/
theorem restrictedIdentity_fst (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentity R n).1 = R.truncation n := sorry

/-- The algebra map of `restrictedIdentity R n` is the canonical quotient map. -/
theorem restrictedIdentity_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentity R n).2.hom =
      Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1)) := sorry

/-- The successor transition of identity truncations in the category of elements of
`restrictedCoyoneda R`. -/
noncomputable def restrictedIdentityMap (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    restrictedIdentity R (n + 1) ⟶ restrictedIdentity R n :=
  CategoryOfElements.homMk (restrictedIdentity R (n + 1)) (restrictedIdentity R n)
    (R.truncationMap n) sorry

/-- The underlying base map of `restrictedIdentityMap` is the truncation projection. -/
theorem restrictedIdentityMap_val (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentityMap R n).val = R.truncationMap n := sorry

/-- Evaluation of a based morphism `φ : underline R |_{C_Λ} ⟶ F` on the identity
truncations of `R`, as a functor `Mor_{C_Λ}(underline R |_{C_Λ}, F) ⟶ hat F(R)`. -/
noncomputable def fromRestrictedHom (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k) :
    RestrictedHom p R ⥤ Functor.Fiber (Functor.completion p) R where
  obj φ :=
    ⟨FormalObject.of R (fun n ↦ φ.obj (restrictedIdentity R n))
        (fun n ↦ φ.map (restrictedIdentityMap R n)) (fun _ ↦ sorry) (fun _ ↦ sorry),
      rfl⟩
  map t :=
    ⟨{ base := 𝟙 R
       app := fun n ↦ t.toNatTrans.app (restrictedIdentity R n)
       baseTrunc := fun n ↦ 𝟙 (R.truncation n)
       over := sorry
       baseTrunc_spec := sorry
       naturality := sorry },
      sorry⟩
  map_id := sorry
  map_comp := sorry

/-- The image of `φ` under `fromRestrictedHom` is a formal object with complete local
base `R`. -/
theorem fromRestrictedHom_obj (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k)
    (φ : RestrictedHom p R) :
    (Functor.Fiber.fiberInclusion.obj ((fromRestrictedHom p R).obj φ)).base = R := sorry

/-- Stage `n` of the image formal object lies over `R.truncation n` and is the value of
`φ` on the `n`th identity truncation. -/
theorem fromRestrictedHom_family (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k)
    (φ : RestrictedHom p R) (n : ℕ) :
    let ξ := Functor.Fiber.fiberInclusion.obj ((fromRestrictedHom p R).obj φ)
    p.obj (ξ.system.family n) = R.truncation n ∧
      ξ.system.family n = φ.obj (restrictedIdentity R n) := sorry

/-- Successor maps of the image formal object are `φ.map` of the truncation projections
and lift `R.truncationMap n`. -/
theorem fromRestrictedHom_step (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k)
    (φ : RestrictedHom p R) (n : ℕ) :
    let ξ := Functor.Fiber.fiberInclusion.obj ((fromRestrictedHom p R).obj φ)
    ξ.system.stepMap n = φ.map (restrictedIdentityMap R n) ∧
      p.IsHomLift (R.truncationMap n) (ξ.system.stepMap n) := sorry

/-- Evaluation of restricted coyoneda morphisms on identity truncations is an
equivalence of categories `Mor_{C_Λ}(underline R |_{C_Λ}, F) ≃ hat F(R)`. -/
instance fromRestrictedHom_isEquivalence (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k) :
    (fromRestrictedHom p R).IsEquivalence := sorry

end

end FormalObject
