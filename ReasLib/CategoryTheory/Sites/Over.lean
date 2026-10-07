module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Comma.Over.Map
public import ReasLib.CategoryTheory.Sites.Over.Continuity
public import ReasLib.CategoryTheory.Sites.Over.Cocontinuity
public import ReasLib.CategoryTheory.Sites.Over.IdentityCover
public import ReasLib.CategoryTheory.Sites.Over.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Over.Pushforward
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import ReasLib.CategoryTheory.Sites.Over.Topos
public import ReasLib.CategoryTheory.Sites.Over.Square
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import ReasLib.CategoryTheory.Sites.Over.Abelian
public import ReasLib.CategoryTheory.Sites.Over.Derived
public import ReasLib.CategoryTheory.Sites.Over.Derived.Unbounded
public import ReasLib.CategoryTheory.Sites.Over.Derived.Square
public import ReasLib.CategoryTheory.Sites.Over.Derived.BaseChange
public import ReasLib.CategoryTheory.Sites.FullyFaithful

/-!
# Slice-site infrastructure

This aggregate reexports the neutral elementary `Over.map` comparisons, the correspondence
between base covers and covers of the identity slice object, and normalization
lemmas for `Over.post`, including continuity, flatness, morphisms of sites,
direct-image comparisons, and coefficientwise sheaf composition under passage
to a slice.
-/

@[expose] public section

universe uC vC uD vD w

namespace CategoryTheory

namespace Over

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

/-- Applying a functor to the triangle equation of a morphism in `Over U` gives the triangle
equation between the corresponding mapped arrows. -/
@[stacks 03CF]
theorem post_map_left_comp_hom
    (u : C ⥤ D) {U : C} {T₁ T₂ : Over U} (g : T₂ ⟶ T₁) :
    u.map g.left ≫ u.map T₁.hom = u.map T₂.hom := sorry

namespace ForgetFullyFaithful

/-- The unique lift of an underlying arrow to a morphism in `Over U` when every arrow into
`U` is unique. -/
noncomputable def preimage (U : C) (hU : ∀ X : C, Subsingleton (X ⟶ U))
    {X Y : Over U} (f : (Over.forget U).obj X ⟶ (Over.forget U).obj Y) : X ⟶ Y :=
  Over.homMk f (Subsingleton.elim _ _)

/-- Forgetting the canonical lifted arrow recovers the original underlying arrow. -/
theorem map_preimage (U : C) (hU : ∀ X : C, Subsingleton (X ⟶ U))
    {X Y : Over U} (f : (Over.forget U).obj X ⟶ (Over.forget U).obj Y) :
    (Over.forget U).map (preimage U hU f) = f := sorry

/-- Canonically lifting the underlying arrow of a slice morphism recovers that morphism. -/
theorem preimage_map (U : C) (hU : ∀ X : C, Subsingleton (X ⟶ U))
    {X Y : Over U} (f : X ⟶ Y) :
    preimage U hU ((Over.forget U).map f) = f := sorry

end ForgetFullyFaithful

/-- If every arrow into `U` is unique, the forgetful functor `Over U ⥤ C` is
fully faithful.  This is explicit evidence rather than a global instance,
since the subsingleton hypothesis is local to an application. -/
@[stacks 0F6Z "fully faithful slice forgetful functor"]
noncomputable def forgetFullyFaithfulOfSubsingletonHom
    (U : C) (hU : ∀ X : C, Subsingleton (X ⟶ U)) :
    (Over.forget U).FullyFaithful where
  preimage := ForgetFullyFaithful.preimage U hU
  map_preimage := ForgetFullyFaithful.map_preimage U hU
  preimage_map := ForgetFullyFaithful.preimage_map U hU

/-- The unit of the continuous sheaf adjunction for `Over.forget U` is invertible when
every morphism into `U` is unique. -/
@[stacks 00Y2 "(1)"]
theorem sheafAdjunctionContinuous_unit_app_isIso_of_subsingletonHom
    (J : GrothendieckTopology C) (U : C) (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [HasWeakSheafify J (Type w)] [HasWeakSheafify (J.over U) (Type w)]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseLeftKanExtension F]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension F]
    (F : Sheaf (J.over U) (Type w)) :
    IsIso (((Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J).unit.app F) := sorry

/-- The counit of the cocontinuous sheaf adjunction for `Over.forget U` is invertible when
every morphism into `U` is unique. -/
@[stacks 00Y2 "(2)"]
theorem sheafAdjunctionCocontinuous_counit_app_isIso_of_subsingletonHom
    (J : GrothendieckTopology C) (U : C) (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension F]
    (F : Sheaf (J.over U) (Type w)) :
    IsIso (((Over.forget U).sheafAdjunctionCocontinuous (Type w) (J.over U) J).counit.app F) := sorry

end Over

end CategoryTheory
