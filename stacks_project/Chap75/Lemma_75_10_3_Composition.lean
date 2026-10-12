/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_27_1_Hom

/-!
# Composition of module pushforwards on algebraic spaces

Module direct image along a composite morphism of algebraic spaces is canonically isomorphic
to the composite of the two direct-image functors. The comparison is assembled from the
underlying type-valued topos pushforwards and the ringed-topos forgetful identifications.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Functor
open Sheaf.InternalModule
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Pushforward of modules along a composite morphism of algebraic spaces is the composite
of the two pushforwards. -/
def pushforwardCompIso {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z) :
    pushforward α ⋙ pushforward β ≅ pushforward (α ≫ β) :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          homOfUnderlying (structureSheaf Z)
            (pushforwardCompHomUnderlying α β M) sorry sorry
        inv :=
          homOfUnderlying (structureSheaf Z)
            (pushforwardCompInvUnderlying α β M) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Forgetting to type-valued sheaves, `pushforwardCompIso` is the composite of
`pushforwardCompForgetIso`, `typePushforwardComp`, and the forgetful iso of the composite. -/
theorem pushforwardCompIso_eq {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z)
    (M : X.Modules) :
    (ToInternal.underlying (structureSheaf Z)).map ((pushforwardCompIso α β).hom.app M) =
      pushforwardCompHomUnderlying α β M :=
  sorry

/-- The component of `pushforwardCompIso` at a module `M` has underlying type-valued
comparison `pushforwardCompHomUnderlying`. -/
theorem pushforwardCompIso_hom_app {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z)
    (M : X.Modules) :
    (ToInternal.underlying (structureSheaf Z)).map ((pushforwardCompIso α β).hom.app M) =
      (pushforwardCompForgetIso α β).hom.app M ≫
        (typePushforwardComp α β).hom.app
          ((ToInternal.underlying (structureSheaf X)).obj M) ≫
        (ModulePushforward.forgetIso (ringedToposHom (α ≫ β))).inv.app M :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
