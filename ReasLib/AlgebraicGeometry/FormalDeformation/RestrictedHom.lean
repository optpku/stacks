/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion

/-!
# Evaluation of restricted coyoneda morphisms

Based functors from the category of elements of a restricted coyoneda functor
evaluate on identity truncations to formal objects over the representing algebra.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

open CompleteLocalAlgCat

noncomputable section

/-- Based functors from the category of elements of the restricted coyoneda of `R`
to a category over Artinian local algebras. -/
abbrev RestrictedHom (p : F ⥤ ArtinianLocalAlgCat Λ k) (R : CompleteLocalAlgCat Λ k) :=
  BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)) ⥤ᵇ
    BasedCategory.ofFunctor p

/-- The canonical quotient of `R` by `maximalIdeal R ^ (n + 1)`, viewed as an
object of the category of elements of its restricted coyoneda. -/
noncomputable def restrictedIdentity (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedCoyoneda R).Elements :=
  ⟨R.truncation n,
    CompleteLocalAlgCat.Hom.of
      (@Ideal.Quotient.mkₐ Λ R.carrier _ _ R.algebra (maximalIdeal R ^ (n + 1)) inferInstance)
      sorry sorry⟩

/-- The base of the identity truncation is the corresponding Artinian truncation. -/
theorem restrictedIdentity_fst (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentity R n).1 = R.truncation n := sorry

/-- The algebra map of the identity truncation is the canonical quotient map. -/
theorem restrictedIdentity_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentity R n).2.hom =
      @Ideal.Quotient.mkₐ Λ R.carrier _ _ R.algebra (maximalIdeal R ^ (n + 1)) inferInstance := sorry

/-- The successor projection between identity truncations in the category of
elements of the restricted coyoneda. -/
noncomputable def restrictedIdentityMap (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    restrictedIdentity R (n + 1) ⟶ restrictedIdentity R n :=
  CategoryOfElements.homMk (restrictedIdentity R (n + 1)) (restrictedIdentity R n)
    (R.truncationMap n) sorry

/-- The base map of the successor projection is the canonical truncation map. -/
theorem restrictedIdentityMap_val (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentityMap R n).val = R.truncationMap n := sorry

/-- Evaluation on identity truncations sends a based functor from the restricted
coyoneda of `R` to a formal object in the completion fibre over `R`. -/
noncomputable def fromRestrictedHom (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k) :
    RestrictedHom p R ⥤ Functor.Fiber (Functor.completion p) R where
  obj φ :=
    ⟨FormalObject.of R (fun n ↦ φ.obj (restrictedIdentity R n))
        (fun n ↦ φ.map (restrictedIdentityMap R n)) (fun _ ↦ sorry) (fun _ ↦ sorry),
      rfl⟩
  map transformation :=
    ⟨FormalObject.Hom.of (𝟙 R)
        (fun n ↦ transformation.toNatTrans.app (restrictedIdentity R n))
        (fun n ↦ 𝟙 (R.truncation n)) sorry sorry sorry,
      sorry⟩
  map_id := sorry
  map_comp := sorry

/-- Evaluation of a restricted coyoneda morphism has complete local base `R`. -/
theorem fromRestrictedHom_obj (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k)
    (φ : RestrictedHom p R) :
    (Functor.Fiber.fiberInclusion.obj ((fromRestrictedHom p R).obj φ)).base = R := sorry

/-- Each stage of an evaluated formal object is the value on the identity
truncation and lies over that truncation. -/
theorem fromRestrictedHom_family (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k)
    (φ : RestrictedHom p R) (n : ℕ) :
    let ξ := Functor.Fiber.fiberInclusion.obj ((fromRestrictedHom p R).obj φ)
    p.obj (ξ.system.family n) = R.truncation n ∧
      ξ.system.family n = φ.obj (restrictedIdentity R n) := sorry

/-- Successor maps of an evaluated formal object are the images of the identity
truncation projections and lift the corresponding truncation maps. -/
theorem fromRestrictedHom_step (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k)
    (φ : RestrictedHom p R) (n : ℕ) :
    let ξ := Functor.Fiber.fiberInclusion.obj ((fromRestrictedHom p R).obj φ)
    ξ.system.stepMap n = φ.map (restrictedIdentityMap R n) ∧
      p.IsHomLift (R.truncationMap n) (ξ.system.stepMap n) := sorry

/-- Evaluation on identity truncations is an equivalence between restricted
coyoneda morphisms and the completion fibre. -/
instance fromRestrictedHom_isEquivalence (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k) :
    (fromRestrictedHom p R).IsEquivalence := sorry

end

end FormalObject
