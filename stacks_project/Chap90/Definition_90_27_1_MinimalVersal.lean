module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_7_3_FormalObject
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck

/-!
# Versal and minimal versal formal objects

A formal object `ξ` of `p` is versal when the morphism associated to `ξ` from the
restricted coyoneda of its base is smooth. It is minimal versal when every morphism
of formal objects into `ξ` is surjective on complete local bases.
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The canonical projection from a complete local algebra to the included `n`th
maximal-adic truncation. -/
noncomputable def truncationToInclusion (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    R ⟶ ArtinianLocalAlgCat.inclusion.obj (R.truncation n) where
  hom := Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1))
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `truncationToInclusion` is the quotient map. -/
theorem truncationToInclusion_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (truncationToInclusion R n).hom =
      Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1)) :=
  sorry

/-- The identity truncation of `R` as an object of the category of elements of
`restrictedCoyoneda R`. -/
noncomputable def identityElement (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (restrictedCoyoneda R).Elements :=
  ⟨R.truncation n, truncationToInclusion R n⟩

/-- The base of `identityElement R n` is the `n`th truncation of `R`. -/
theorem identityElement_base (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (identityElement R n).1 = R.truncation n :=
  sorry

/-- The successor transition of identity truncations, as a morphism in the category
of elements of `restrictedCoyoneda R`. -/
noncomputable def identityElementMap (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    identityElement R (n + 1) ⟶ identityElement R n :=
  ⟨R.truncationMap n, sorry⟩

/-- The underlying base map of `identityElementMap` is the truncation projection. -/
theorem identityElementMap_val (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (identityElementMap R n).val = R.truncationMap n :=
  sorry

/-- The Hom-universe lift of the category of elements of `restrictedCoyoneda R`,
used to match the universe constraint of `FormalObject`. -/
abbrev identityTotal (R : CompleteLocalAlgCat Λ k) : Type (u + 1) :=
  ULiftHom.{u + 1} (restrictedCoyoneda R).Elements

/-- `identityTotal R` is the Hom-universe lift of the category of elements of
`restrictedCoyoneda R`. -/
theorem identityTotal_eq (R : CompleteLocalAlgCat Λ k) :
    identityTotal R = ULiftHom.{u + 1} (restrictedCoyoneda R).Elements :=
  sorry

/-- Projection of the Hom-universe lift of identity truncations to `C_Λ`. -/
noncomputable def identityProjection (R : CompleteLocalAlgCat Λ k) :
    identityTotal R ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : identityTotal R ⥤ (restrictedCoyoneda R).Elements) ⋙
    CategoryOfElements.π (restrictedCoyoneda R)

/-- `identityProjection` is the category-of-elements projection after Hom-universe
forgetful. -/
theorem identityProjection_eq (R : CompleteLocalAlgCat Λ k) :
    identityProjection R =
      (ULiftHom.down : identityTotal R ⥤ (restrictedCoyoneda R).Elements) ⋙
        CategoryOfElements.π (restrictedCoyoneda R) :=
  sorry

/-- Stage `n` of the identity formal object in the Hom-universe lift. -/
noncomputable def identityStage (R : CompleteLocalAlgCat Λ k) (n : ℕ) : identityTotal R :=
  ULiftHom.objUp (identityElement R n)

/-- `identityStage R n` is the Hom-universe lift of `identityElement R n`. -/
theorem identityStage_eq (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    identityStage R n = ULiftHom.objUp (identityElement R n) :=
  sorry

/-- Successor transition of identity stages in the Hom-universe lift. -/
noncomputable def identityStageMap (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    identityStage R (n + 1) ⟶ identityStage R n :=
  (ULiftHom.up : (restrictedCoyoneda R).Elements ⥤ identityTotal R).map
    (identityElementMap R n)

/-- `identityStageMap` is the image of `identityElementMap` under `ULiftHom.up`. -/
theorem identityStageMap_eq (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    identityStageMap R n =
      (ULiftHom.up : (restrictedCoyoneda R).Elements ⥤ identityTotal R).map
        (identityElementMap R n) :=
  sorry

/-- The identity formal object of `restrictedCoyoneda R`, given by the identity
truncations of `R`. -/
noncomputable def identityFormalObject (R : CompleteLocalAlgCat Λ k) :
    FormalObject (identityProjection R) where
  base := R
  system := Functor.ofOpSequence (identityStageMap R)
  over_obj := sorry
  over_step := sorry

/-- The complete local base of `identityFormalObject R` is `R`. -/
theorem identityFormalObject_base (R : CompleteLocalAlgCat Λ k) :
    (identityFormalObject R).base = R :=
  sorry

/-- Stage `n` of `identityFormalObject R` lies over the `n`th truncation of `R`. -/
theorem identityFormalObject_spec (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (identityProjection R).obj ((identityFormalObject R).system.family n) =
        R.truncation n ∧
      (identityProjection R).IsHomLift (R.truncationMap n)
        ((identityFormalObject R).system.stepMap n) :=
  sorry

/-- The category of elements of `restrictedCoyoneda R`, after Hom-universe lift, is
cofibered in groupoids over `C_Λ`. -/
instance identityProjection_op_inGroupoids (R : CompleteLocalAlgCat Λ k) :
    Functor.IsFibered.InGroupoids (identityProjection R).op :=
  sorry

end CompleteLocalAlgCat

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- A based functor `φ` represents a formal object `ξ` when it sends the identity
truncations of `ξ.base` to the stages of `ξ`. -/
def Represents (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
        BasedCategory.ofFunctor p) : Prop :=
  ∃ h : ∀ n : ℕ, φ.obj (CompleteLocalAlgCat.identityStage ξ.base n) = ξ.system.family n,
    ∀ n : ℕ,
      φ.map (CompleteLocalAlgCat.identityStageMap ξ.base n) =
        eqToHom (h (n + 1)) ≫ ξ.system.stepMap n ≫ eqToHom (h n).symm

/-- A representing based functor sends identity truncations to the stages of `ξ`. -/
theorem represents_obj (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
        BasedCategory.ofFunctor p) (hφ : Represents ξ φ) (n : ℕ) :
    φ.obj (CompleteLocalAlgCat.identityStage ξ.base n) = ξ.system.family n :=
  sorry

/-- A formal object is versal when it is represented by a smooth morphism from the
restricted coyoneda of its complete local base. -/
class IsVersal (ξ : FormalObject p) [Functor.IsFibered.InGroupoids p.op] : Prop where
  /-- There is a smooth based functor representing `ξ`. -/
  exists_smooth_representation :
    ∃ φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
        BasedCategory.ofFunctor p,
      Represents ξ φ ∧ BasedFunctor.IsSmooth φ

/-- Versality supplies a smooth representing based functor from the restricted
coyoneda of the complete local base. -/
theorem IsVersal.spec (ξ : FormalObject p) [Functor.IsFibered.InGroupoids p.op]
    [IsVersal ξ] :
    ∃ φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
        BasedCategory.ofFunctor p,
      Represents ξ φ ∧ BasedFunctor.IsSmooth φ :=
  sorry

/-- A versal formal object is minimal when every morphism of formal objects into it
is surjective on complete local bases. -/
class IsMinimalVersal (ξ : FormalObject p) [Functor.IsFibered.InGroupoids p.op] : Prop
    extends IsVersal ξ where
  /-- Every morphism of formal objects into `ξ` is surjective on underlying algebras. -/
  surjective_base : ∀ {η : FormalObject p} (f : η ⟶ ξ), Function.Surjective f.base.hom

/-- Morphisms of formal objects into a minimal versal formal object are surjective
on complete local bases. -/
theorem IsMinimalVersal.spec (ξ : FormalObject p) [Functor.IsFibered.InGroupoids p.op]
    [IsMinimalVersal ξ] {η : FormalObject p} (f : η ⟶ ξ) :
    Function.Surjective f.base.hom :=
  sorry

end FormalObject

namespace CompleteLocalAlgCat

/-- The identity based functor of `identityProjection R` represents `identityFormalObject R`. -/
theorem identityFormalObject_represents (R : CompleteLocalAlgCat Λ k) :
    FormalObject.Represents (identityFormalObject R)
      (BasedFunctor.id (BasedCategory.ofFunctor (identityProjection R))) :=
  sorry

/-- The identity formal object of a restricted coyoneda functor is versal. -/
instance instIsVersalIdentityFormalObject (R : CompleteLocalAlgCat Λ k) :
    FormalObject.IsVersal (identityFormalObject R) :=
  sorry

/-- The identity formal object of a restricted coyoneda functor is minimal versal. -/
instance instIsMinimalVersalIdentityFormalObject (R : CompleteLocalAlgCat Λ k) :
    FormalObject.IsMinimalVersal (identityFormalObject R) :=
  sorry

end CompleteLocalAlgCat
