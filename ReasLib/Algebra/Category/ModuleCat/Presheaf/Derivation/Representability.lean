module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Representability of presheaf derivations

This file packages the universal derivation interface from mathlib as a reusable target functor,
Hom equivalence, and `CorepresentableBy` witness.  Sheaf-level relative differentials specialize
this API while retaining their own sheafification bridge.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.Derivation'

variable {C : Type u} [Category.{v} C]
variable {S R : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Postcomposition sends a presheaf relative derivation to one with a new target module. -/
@[stacks 04BL "presheaf derivation postcomposition"]
noncomputable def map (φ : S ⟶ R)
    {M N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) : M.Derivation' φ ⟶ N.Derivation' φ :=
  TypeCat.ofHom fun D ↦ D.postcomp f

/-- Postcomposition by an identity is the identity on presheaf relative derivations. -/
@[simp]
theorem map_id (φ : S ⟶ R)
    (M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    map φ (𝟙 M) = 𝟙 (M.Derivation' φ) := sorry

/-- Successive postcomposition of presheaf relative derivations agrees with composition of target
module morphisms. -/
@[simp]
theorem map_comp (φ : S ⟶ R)
    {M N P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) (g : N ⟶ P) :
    map φ (f ≫ g) = map φ f ≫ map φ g := sorry

/-- The Type-valued functor of presheaf relative derivations with varying target module. -/
@[stacks 04BL "presheaf derivation functor"]
noncomputable def functor (φ : S ⟶ R) :
    PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) ⥤ Type _ where
  obj M := M.Derivation' φ
  map f := map φ f
  map_id M := map_id φ M
  map_comp f g := map_comp φ f g

/-- The functorial action on a presheaf derivation is postcomposition. -/
@[simp]
theorem functor_map_apply (φ : S ⟶ R)
    {M N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) (D : M.Derivation' φ) :
    (functor φ).map f D = D.postcomp f := sorry

/-- A universal presheaf derivation gives the representing Hom equivalence. -/
@[stacks 04BL "universal presheaf derivation equivalence"]
noncomputable def Universal.homEquiv
    {M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    {φ : S ⟶ R} (d : M.Derivation' φ) (h : d.Universal)
    (N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    (M ⟶ N) ≃ N.Derivation' φ where
  toFun f := d.postcomp f
  invFun := h.desc
  left_inv f := h.postcomp_injective _ _ (h.fac (d.postcomp f))
  right_inv := h.fac

/-- The forward map of the universal derivation equivalence is postcomposition. -/
@[simp]
theorem Universal.homEquiv_apply
    {M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    {φ : S ⟶ R} (d : M.Derivation' φ) (h : d.Universal)
    (N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (f : M ⟶ N) :
    Universal.homEquiv d h N f = d.postcomp f := sorry

/-- The inverse map of the universal derivation equivalence is the universal desc map. -/
@[simp]
theorem Universal.homEquiv_symm_apply
    {M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    {φ : S ⟶ R} (d : M.Derivation' φ) (h : d.Universal)
    (N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (D : N.Derivation' φ) :
    (Universal.homEquiv d h N).symm D = h.desc D := sorry

/-- The universal Hom equivalence is natural in its target module. -/
@[stacks 04BL "universal derivation Hom naturality"]
theorem Universal.homEquiv_comp
    {M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    {φ : S ⟶ R} (d : M.Derivation' φ) (h : d.Universal)
    {N P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (g : N ⟶ P) (f : M ⟶ N) :
    Universal.homEquiv d h P (f ≫ g) =
      (functor φ).map g (Universal.homEquiv d h N f) := sorry

/-- A universal presheaf derivation corepresents the target derivation functor. -/
@[stacks 04BL "corepresented presheaf derivations"]
noncomputable def Universal.corepresentableBy
    {M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    {φ : S ⟶ R} (d : M.Derivation' φ) (h : d.Universal) :
    (functor φ).CorepresentableBy M where
  homEquiv := Universal.homEquiv d h _
  homEquiv_comp := Universal.homEquiv_comp d h

end PresheafOfModules.Derivation'
