module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

/-!
# Sections with proper support on the small étale site

For a locally finite-type scheme morphism, sections of the abelian small-étale
direct image whose supports are proper over the base form additive subgroups
and a subfunctor satisfying the sheaf condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- A section of the abelian étale direct image has proper support over a base object
when its closed section support on the étale base change is proper over that object. -/
def HasProperSupport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) : Prop :=
  ClosedSubset.IsProperOver (pullback.fst V.hom f)
    (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ)

/-- Proper support of a pushforward section is properness of its étale section
support over the base. -/
theorem hasProperSupport_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    HasProperSupport f F V σ ↔
      ClosedSubset.IsProperOver (pullback.fst V.hom f)
        (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ) := sorry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- The zero section of an abelian étale direct image has proper support. -/
theorem zero_mem_properSupportSections (V : Y.Etale) :
    HasProperSupport f F V 0 := sorry

/-- Properly supported sections of an abelian étale direct image are closed under addition. -/
theorem add_mem_properSupportSections (V : Y.Etale)
    {σ τ : (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj F).1.obj (op V)}
    (hσ : HasProperSupport f F V σ) (hτ : HasProperSupport f F V τ) :
    HasProperSupport f F V (σ + τ) := sorry

/-- Properly supported sections of an abelian étale direct image are closed under negation. -/
theorem neg_mem_properSupportSections (V : Y.Etale)
    {σ : (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj F).1.obj (op V)}
    (hσ : HasProperSupport f F V σ) :
    HasProperSupport f F V (-σ) := sorry

/-- The additive subgroup of sections of the abelian étale direct image having support
proper over a given étale object of the base. -/
def properSupportSections (V : Y.Etale) :
    AddSubgroup ((((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj F).1.obj (op V)) where
  carrier := {σ | HasProperSupport f F V σ}
  zero_mem' := zero_mem_properSupportSections f F V
  add_mem' := fun hσ hτ => add_mem_properSupportSections f F V hσ hτ
  neg_mem' := fun hσ => neg_mem_properSupportSections f F V hσ

/-- Membership in the proper-support subgroup is the proper-support condition. -/
theorem mem_properSupportSections_iff (V : Y.Etale)
    (σ : (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj F).1.obj (op V)) :
    σ ∈ properSupportSections f F V ↔ HasProperSupport f F V σ := Iff.rfl

/-- Restriction of a properly supported direct-image section along an étale base morphism
again has proper support. -/
theorem properSupportSubfunctor_map {V W : Y.Etaleᵒᵖ} (g : V ⟶ W)
    (σ : (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj F).1.obj V)
    (hσ : HasProperSupport f F V.unop σ) :
    HasProperSupport f F W.unop
      ((((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology).obj F).1.map g σ) := sorry

/-- The subfunctor of the type-valued abelian étale direct image consisting of sections
whose closed supports are proper over the base. -/
def properSupportSubfunctor :
    Subfunctor (((((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj F).obj) ⋙
        CategoryTheory.forget AddCommGrpCat) where
  obj W := {σ | HasProperSupport f F W.unop σ}
  map := fun g σ hσ => properSupportSubfunctor_map f F g σ hσ

/-- Objectwise, the proper-support subfunctor consists precisely of sections with proper
support over the corresponding object of the étale base. -/
theorem properSupportSubfunctor_obj (V : Y.Etale) :
    (properSupportSubfunctor f F).obj (op V) =
      {σ | HasProperSupport f F V σ} := rfl

/-- Membership in the proper-support subfunctor agrees with membership in the additive
subgroup of properly supported sections. -/
theorem mem_properSupportSubfunctor_obj_iff (V : Y.Etale)
    (σ : (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj F).1.obj (op V)) :
    σ ∈ (properSupportSubfunctor f F).obj (op V) ↔
      σ ∈ properSupportSections f F V := Iff.rfl

/-- Sections of an abelian étale direct image with support proper over the base form a
sheaf on the small étale site; no separatedness assumption on the morphism is needed. -/
theorem isSheaf_properSupportSubfunctor :
    Presieve.IsSheaf Y.smallEtaleTopology (properSupportSubfunctor f F).toFunctor := sorry

end AlgebraicGeometry.Scheme.Etale

end
