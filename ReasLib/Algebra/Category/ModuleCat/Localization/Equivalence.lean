module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.RingTheory.Localization.Module
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.RingTheory.Algebra.IsEpi.Localization.Basic
public import ReasLib.RingTheory.Algebra.IsEpi.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules over a Localization

Modules over any localization of `R` at `S` are equivalent to the `R`-modules
on which every element of `S` acts invertibly.

@stack 07JY
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace ModuleCat.Localization

variable {R : Type u} [CommRing R]

/-- The property that every element of `S` acts invertibly on an `R`-module. -/
@[stacks 07JY "modules inverting a submonoid"]
def inverting (S : Submonoid R) : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ ∀ s : S, IsUnit (algebraMap R (Module.End R M) s)

/-- The full subcategory of modules on which every element of `S` acts invertibly. -/
@[stacks 07JY "modules inverting a submonoid"]
abbrev Inverting (S : Submonoid R) :=
  (inverting.{u, v} S).FullSubcategory

/-- The identity is a localization map exactly when all denominators act invertibly. -/
@[stacks 07JY "identity localized-module criterion"]
theorem isLocalizedModule_id_iff (S : Submonoid R) (M : ModuleCat.{v} R) :
    IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) ↔ inverting S M :=
  by
    constructor
    · intro h
      exact h.map_units
    · intro h
      exact
        { map_units := h
          surj := fun m ↦ ⟨(m, 1), by simp⟩
          exists_of_eq := fun h ↦ ⟨1, by simpa using h⟩ }

/-- Invertibility of the `S`-action is invariant under module isomorphism. -/
@[stacks 07JY "invertible action isomorphism invariance"]
instance inverting.isClosedUnderIsomorphisms (S : Submonoid R) :
    (inverting.{u, v} S).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX s := by
    refine (Module.End.isUnit_iff _).2 ?_
    have hs := (Module.End.isUnit_iff _).1 (hX s)
    constructor
    · intro y₁ y₂ hy
      apply e.symm.toLinearEquiv.injective
      apply hs.1
      simpa using congr_arg e.symm.toLinearEquiv hy
    · intro y
      obtain ⟨x, hx⟩ := hs.2 (e.symm.toLinearEquiv y)
      refine ⟨e.toLinearEquiv x, ?_⟩
      apply e.symm.toLinearEquiv.injective
      simpa using hx

variable (S : Submonoid R) (A : Type w)
variable [CommRing A] [Algebra R A] [IsLocalization S A]

/-- Restriction from a localization lands in modules inverting `S`. -/
@[stacks 07JY "localized module restricts to invertible action"]
theorem restrict_obj_mem (M : ModuleCat.{v} A) :
    inverting S ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
  (isLocalizedModule_id_iff S _).1 (isLocalizedModule_id S M A)

/-- Restriction of scalars, with codomain narrowed to modules inverting `S`. -/
@[stacks 07JY "restriction to modules inverting the denominators"]
noncomputable abbrev restrict :
    ModuleCat.{v} A ⥤ Inverting.{u, v} S :=
  (inverting S).lift
    (ModuleCat.restrictScalars (algebraMap R A))
    (restrict_obj_mem S A)

namespace restrict

/-- Fullness is inherited from the algebra-epimorphism property of a localization. -/
@[stacks 07JY "fullness of localization restriction"]
instance full : (restrict.{u, v, w} S A).Full where
  map_surjective := by
    intro M N f
    obtain ⟨g, hg⟩ :=
      (Algebra.IsEpi.restrictScalars_full
        (Algebra.IsEpi.of_isLocalization S A)).map_surjective f.hom
    refine ⟨g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

/-- Forgetting the invertibility witness recovers ordinary restriction of scalars. -/
@[simp, stacks 07JY "restriction followed by inclusion"]
theorem comp_ι :
    restrict.{u, v, w} S A ⋙ (inverting S).ι =
      ModuleCat.restrictScalars (algebraMap R A) :=
  rfl

/-- Every module inverting `S` comes from a module over the localization. -/
@[stacks 07JY "essential surjectivity of localization restriction"]
instance essSurj : (restrict.{u, v, w} S A).EssSurj where
  mem_essImage := by
    intro M
    -- Local instance justification (proof-local temporary data): Mathlib's induced
    -- localization action consumes the identity-localization property as a class.
    letI : IsLocalizedModule S (LinearMap.id : M.obj →ₗ[R] M.obj) :=
      (isLocalizedModule_id_iff S M.obj).2 M.property
    -- Local instance justification (instance diamond): the induced `A`-action must not
    -- compete globally with the existing `R`-action on the same carrier.
    letI : Module A M.obj :=
      IsLocalizedModule.module S (LinearMap.id : M.obj →ₗ[R] M.obj)
    -- Local instance justification (instance diamond): this compatibility belongs to
    -- the just-selected localization action and cannot be a global carrier instance.
    letI : IsScalarTower R A M.obj :=
      IsLocalizedModule.isScalarTower_module S
        (LinearMap.id : M.obj →ₗ[R] M.obj)
    refine ⟨ModuleCat.of A M.obj, ?_⟩
    refine ⟨(inverting S).isoMk ?_⟩
    exact
      { hom := ConcreteCategory.ofHom
          { toFun := fun x ↦ x
            map_add' := by intro x y; rfl
            map_smul' := by
              intro r x
              change (algebraMap R A r) • (show M.obj from x) =
                r • (show M.obj from x)
              exact IsScalarTower.algebraMap_smul A r (show M.obj from x) }
        inv := ConcreteCategory.ofHom
          { toFun := fun x ↦ x
            map_add' := by intro x y; rfl
            map_smul' := by
              intro r x
              change r • x = (algebraMap R A r) • x
              exact (IsScalarTower.algebraMap_smul A r x).symm } }

/-- Restriction from a localization is an equivalence. -/
@[stacks 07JY "localization restriction is an equivalence"]
instance isEquivalence : (restrict.{u, v, w} S A).IsEquivalence := {}

/-- Denominators act invertibly on every restricted module. -/
@[stacks 07JY "denominators act invertibly after restriction"]
theorem obj_isUnit (M : ModuleCat.{v} A) (s : S) :
    IsUnit
      (algebraMap R
        (Module.End R ((restrict S A).obj M).obj) s) :=
  ((restrict S A).obj M).property s

end restrict

/-- Modules over any model of `S⁻¹R` are equivalent to modules inverting `S`. -/
@[stacks 07JY "module category of a localization"]
noncomputable def equivalence :
    ModuleCat.{v} A ≌ Inverting.{u, v} S :=
  (restrict S A).asEquivalence

/-- The forward functor is restriction of scalars with narrowed codomain. -/
@[simp, stacks 07JY "localization equivalence forward functor"]
theorem equivalence_functor :
    (equivalence.{u, v, w} S A).functor = restrict S A :=
  rfl

#synth (ModuleCat.Localization.restrict.{u, v, w} S A).Faithful
#synth (ModuleCat.Localization.restrict.{u, v, w} S A).Full
#synth (ModuleCat.Localization.restrict.{u, v, w} S A).IsEquivalence

end ModuleCat.Localization
