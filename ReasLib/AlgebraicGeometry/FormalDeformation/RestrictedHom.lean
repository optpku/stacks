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

/-- The canonical quotient map to an Artinian truncation is local. -/
theorem restrictedIdentity_local (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsLocalHom (@Ideal.Quotient.mkₐ Λ R.carrier _ _ R.algebra
      (maximalIdeal R ^ (n + 1)) inferInstance) := sorry

/-- The canonical quotient map respects the chosen residue identifications. -/
theorem restrictedIdentity_residue (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    CompleteLocalAlgCat.residueCompat (A := R)
      (B := ArtinianLocalAlgCat.inclusion.obj (R.truncation n))
      (@Ideal.Quotient.mkₐ Λ R.carrier _ _ R.algebra (maximalIdeal R ^ (n + 1)) inferInstance)
      (restrictedIdentity_local R n) =
      CompleteLocalAlgCat.residueIsoHom R := sorry

/-- The identity truncation element is the canonical quotient map from its base. -/
noncomputable def restrictedIdentity (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedCoyoneda R).Elements :=
  ⟨R.truncation n, CompleteLocalAlgCat.Hom.of
    (@Ideal.Quotient.mkₐ Λ R.carrier _ _ R.algebra (maximalIdeal R ^ (n + 1)) inferInstance)
    (restrictedIdentity_local R n) (restrictedIdentity_residue R n)⟩

/-- The base of an identity truncation is the corresponding Artinian truncation. -/
theorem restrictedIdentity_fst (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentity R n).1 = R.truncation n := sorry

/-- The algebra map of the identity truncation is the canonical quotient map. -/
theorem restrictedIdentity_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentity R n).2.hom =
      @Ideal.Quotient.mkₐ Λ R.carrier _ _ R.algebra
        (maximalIdeal R ^ (n + 1)) inferInstance := sorry

/-- The successor truncation projection carries the identity element to the identity element. -/
theorem restrictedIdentityMap_property (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedCoyoneda R).map (R.truncationMap n)
      (restrictedIdentity R (n + 1)).2 = (restrictedIdentity R n).2 := sorry

/-- The successor projection between identity truncation elements. -/
noncomputable def restrictedIdentityMap (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    restrictedIdentity R (n + 1) ⟶ restrictedIdentity R n :=
  CategoryOfElements.homMk _ _ (R.truncationMap n) (restrictedIdentityMap_property R n)

/-- The base map of the successor projection is the canonical truncation map. -/
theorem restrictedIdentityMap_val (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedIdentityMap R n).val = R.truncationMap n := sorry

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
  (R : CompleteLocalAlgCat Λ k)

/-- Evaluation of a based functor on an identity truncation lies over that truncation. -/
theorem fromRestrictedHom_obj_over (φ : RestrictedHom p R) (n : ℕ) :
    p.obj (φ.obj (restrictedIdentity R n)) = R.truncation n := sorry

/-- Evaluation of an identity successor map lifts the truncation projection. -/
theorem fromRestrictedHom_step_over (φ : RestrictedHom p R) (n : ℕ) :
    p.IsHomLift (R.truncationMap n) (φ.map (restrictedIdentityMap R n)) := sorry

/-- The formal object obtained by evaluating a based functor on identity truncations. -/
noncomputable def fromRestrictedHomObject (φ : RestrictedHom p R) : FormalObject p :=
  FormalObject.of R (fun n ↦ φ.obj (restrictedIdentity R n))
    (fun n ↦ φ.map (restrictedIdentityMap R n))
    (fromRestrictedHom_obj_over p R φ) (fromRestrictedHom_step_over p R φ)

/-- Evaluation of a based natural transformation has vertical stage maps. -/
theorem fromRestrictedHom_map_over {φ ψ : RestrictedHom p R} (transformation : φ ⟶ ψ)
    (n : ℕ) : p.IsHomLift (𝟙 (R.truncation n))
      (transformation.toNatTrans.app (restrictedIdentity R n)) := sorry

/-- Identity truncated base maps satisfy the quotient square for an evaluated transformation. -/
theorem fromRestrictedHom_map_baseTrunc_spec (n : ℕ) :
    (ArtinianLocalAlgCat.Hom.toRingHom (𝟙 (R.truncation n))).comp
      (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) =
    (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))).comp
      (CompleteLocalAlgCat.Hom.toRingHom (𝟙 R)) := sorry

/-- Evaluated natural transformations commute with successor maps. -/
theorem fromRestrictedHom_map_naturality {φ ψ : RestrictedHom p R}
    (transformation : φ ⟶ ψ) (n : ℕ) :
    (fromRestrictedHomObject p R φ).system.stepMap n ≫
      transformation.toNatTrans.app (restrictedIdentity R n) =
    transformation.toNatTrans.app (restrictedIdentity R (n + 1)) ≫
      (fromRestrictedHomObject p R ψ).system.stepMap n := sorry

/-- Evaluation of a based natural transformation gives a formal-object morphism. -/
noncomputable def fromRestrictedHomMap {φ ψ : RestrictedHom p R} (transformation : φ ⟶ ψ) :
    fromRestrictedHomObject p R φ ⟶ fromRestrictedHomObject p R ψ :=
  FormalObject.Hom.of (𝟙 R)
    (fun n ↦ transformation.toNatTrans.app (restrictedIdentity R n))
    (fun n ↦ 𝟙 (R.truncation n)) (fromRestrictedHom_map_over p R transformation)
    (fromRestrictedHom_map_baseTrunc_spec R) (fromRestrictedHom_map_naturality p R transformation)

/-- Evaluated transformations lift the identity on the complete local base. -/
theorem fromRestrictedHom_map_base {φ ψ : RestrictedHom p R} (transformation : φ ⟶ ψ) :
    (Functor.completion p).IsHomLift (𝟙 R) (fromRestrictedHomMap p R transformation) := sorry

/-- Evaluation of a based functor as an object in the completion fibre. -/
noncomputable def fromRestrictedHomFiberObject (φ : RestrictedHom p R) :
    Functor.Fiber (Functor.completion p) R := ⟨fromRestrictedHomObject p R φ, rfl⟩

/-- Evaluation of a transformation as a morphism in the completion fibre. -/
noncomputable def fromRestrictedHomFiberMap {φ ψ : RestrictedHom p R}
    (transformation : φ ⟶ ψ) :
    fromRestrictedHomFiberObject p R φ ⟶ fromRestrictedHomFiberObject p R ψ :=
  ⟨fromRestrictedHomMap p R transformation, fromRestrictedHom_map_base p R transformation⟩

/-- Evaluation preserves identity transformations in the completion fibre. -/
theorem fromRestrictedHom_map_id (φ : RestrictedHom p R) :
    fromRestrictedHomFiberMap p R (𝟙 φ) = 𝟙 (fromRestrictedHomFiberObject p R φ) := sorry

/-- Evaluation preserves composition of transformations in the completion fibre. -/
theorem fromRestrictedHom_map_comp {φ ψ χ : RestrictedHom p R}
    (first : φ ⟶ ψ) (second : ψ ⟶ χ) :
    fromRestrictedHomFiberMap p R (first ≫ second) =
      fromRestrictedHomFiberMap p R first ≫ fromRestrictedHomFiberMap p R second := sorry

/-- Evaluation on identity truncations takes based functors to the completion fibre. -/
noncomputable def fromRestrictedHom : RestrictedHom p R ⥤ Functor.Fiber (Functor.completion p) R where
  obj := fromRestrictedHomFiberObject p R
  map := fromRestrictedHomFiberMap p R
  map_id := fromRestrictedHom_map_id p R
  map_comp := fromRestrictedHom_map_comp p R

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
