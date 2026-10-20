/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition

/-!
# Pullbacks of meromorphic functions

This file records the nonzerodivisor denominator system on opens of a locally ringed space and the
condition ensuring that a morphism preserves chosen denominator systems under pullback.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

namespace Hom

variable {X Y : LocallyRingedSpace.{u}}

/-- Pull a section on `V` back along `f` to `f⁻¹(V)` and then restrict it to `U ⊆ f⁻¹(V)`. -/
@[stacks 02OT "section pullback on nested opens"]
abbrev pullbackSection
    (f : X ⟶ Y)
    {U : Opens X} {V : Opens Y}
    (e : U ≤ (Opens.map f.base).obj V) :
    Y.presheaf.obj (op V) ⟶ X.presheaf.obj (op U) :=
  f.c.app (op V) ≫ X.presheaf.map (homOfLE e).op

/-- Pullbacks of meromorphic functions are defined for `f : X ⟶ Y` when pullback carries every
chosen regular denominator on `V` to a chosen regular denominator on each
`U ⊆ f⁻¹(V)`. -/
def pullbacksMeromorphicFunctionsDefined
    (f : X ⟶ Y)
    (regularSectionsX :
      ∀ U : Opens X, Set (X.presheaf.obj (op U)))
    (regularSectionsY :
      ∀ V : Opens Y, Set (Y.presheaf.obj (op V))) : Prop :=
  ∀ ⦃U : Opens X⦄ ⦃V : Opens Y⦄
    (e : U ≤ (Opens.map f.base).obj V)
    ⦃s : Y.presheaf.obj (op V)⦄,
      s ∈ regularSectionsY V →
        pullbackSection f e s ∈ regularSectionsX U

/-- Pullbacks of regular meromorphic functions are defined when pullback preserves the canonical
stalkwise non-zero-divisor denominator presheaves. -/
@[stacks 02OT]
abbrev pullbacksRegularMeromorphicFunctionsDefined (f : X ⟶ Y) : Prop :=
  pullbacksMeromorphicFunctionsDefined f
    (fun U ↦ (X.meromorphicFunctionDenominators).obj (op U))
    (fun V ↦ (Y.meromorphicFunctionDenominators).obj (op V))

/-- Pullback preserves regular meromorphic functions exactly when it carries every canonical
denominator section on `V` to one on each `U ⊆ f⁻¹(V)`. -/
theorem pullbacksRegularMeromorphicFunctionsDefined_iff (f : X ⟶ Y) :
    pullbacksRegularMeromorphicFunctionsDefined f ↔
      ∀ ⦃U : Opens X⦄ ⦃V : Opens Y⦄
        (e : U ≤ (Opens.map f.base).obj V)
        ⦃s : Y.presheaf.obj (op V)⦄,
          s ∈ (Y.meromorphicFunctionDenominators).obj (op V) →
            pullbackSection f e s ∈
              (X.meromorphicFunctionDenominators).obj (op U) := sorry

/-- Apply the pullback condition to a specified regular section on `V`. -/
theorem pullbackSection_mem_regularSections
    {f : X ⟶ Y}
    {regularSectionsX :
      ∀ U : Opens X, Set (X.presheaf.obj (op U))}
    {regularSectionsY :
      ∀ V : Opens Y, Set (Y.presheaf.obj (op V))}
    (hf : pullbacksMeromorphicFunctionsDefined f regularSectionsX regularSectionsY)
    {U : Opens X} {V : Opens Y}
    (e : U ≤ (Opens.map f.base).obj V)
    {s : Y.presheaf.obj (op V)}
    (hs : s ∈ regularSectionsY V) :
    X.presheaf.map (homOfLE e).op ((f.c.app (op V)) s) ∈ regularSectionsX U :=
  hf e hs

/-- A morphism preserving regular meromorphic functions pulls a denominator section on `V` back
to a denominator section on every `U ⊆ f⁻¹(V)`. -/
theorem pullbackSection_mem_meromorphicFunctionDenominators
    {f : X ⟶ Y}
    (hf : pullbacksRegularMeromorphicFunctionsDefined f)
    {U : Opens X} {V : Opens Y}
    (e : U ≤ (Opens.map f.base).obj V)
    {s : Y.presheaf.obj (op V)}
    (hs : s ∈ (Y.meromorphicFunctionDenominators).obj (op V)) :
    X.presheaf.map (homOfLE e).op ((f.c.app (op V)) s) ∈
      (X.meromorphicFunctionDenominators).obj (op U) :=
  hf e hs

/-- The localization map on total quotient rings over an open subset induced by a morphism that
preserves the canonical meromorphic denominators. -/
noncomputable def meromorphicFunctionPresheafMapApp
    (f : X ⟶ Y) (hf : pullbacksRegularMeromorphicFunctionsDefined f)
    (V : (Opens Y)ᵒᵖ) :
    (TopCat.Presheaf.totalQuotientPresheaf Y.𝒪.presheaf).obj V ⟶
      (TopCat.Presheaf.totalQuotientPresheaf X.𝒪.presheaf).obj
        ((Opens.map f.base).op.obj V) :=
  CommRingCat.ofHom <| IsLocalization.map
    (M := (Y.meromorphicFunctionDenominators).obj V)
    (S := Localization ((Y.meromorphicFunctionDenominators).obj V))
    (T := (X.meromorphicFunctionDenominators).obj ((Opens.map f.base).op.obj V))
    (Localization ((X.meromorphicFunctionDenominators).obj
      ((Opens.map f.base).op.obj V))) (f.c.app V).hom <| by
        intro s hs
        let U := (Opens.map f.base).obj V.unop
        change (f.c.app V).hom s ∈
          (X.meromorphicFunctionDenominators).obj (op U)
        let e : U ≤ (Opens.map f.base).obj V.unop := le_refl U
        have h := pullbackSection_mem_meromorphicFunctionDenominators
          (U := U) (V := V.unop) hf e hs
        have hi : (homOfLE e).op = 𝟙 (op U) := Subsingleton.elim _ _
        have hm : X.presheaf.map (homOfLE e).op = 𝟙 _ :=
          (congrArg (fun k : op U ⟶ op U ↦ X.presheaf.map k) hi).trans
            (X.presheaf.map_id (op U))
        have hm_app := congrArg
          (fun q : X.presheaf.obj (op U) ⟶ X.presheaf.obj (op U) ↦
            ConcreteCategory.hom q
            (ConcreteCategory.hom (f.c.app (op V.unop)) s)) hm
        have h' := hm_app ▸ h
        have hid_app :
            ConcreteCategory.hom (𝟙 (X.presheaf.obj (op U)))
                (ConcreteCategory.hom (f.c.app (op V.unop)) s) =
              ConcreteCategory.hom (f.c.app (op V.unop)) s := rfl
        exact hid_app ▸ h'

/-- The maps on total quotient rings induced by pullback commute with restriction to smaller
open subsets. -/
theorem meromorphicFunctionPresheafMap_naturality
    (f : X ⟶ Y) (hf : pullbacksRegularMeromorphicFunctionsDefined f)
    {V W : (Opens Y)ᵒᵖ} (i : V ⟶ W) :
    (TopCat.Presheaf.totalQuotientPresheaf Y.𝒪.presheaf).map i ≫
        meromorphicFunctionPresheafMapApp f hf W =
      meromorphicFunctionPresheafMapApp f hf V ≫
        (TopCat.Presheaf.totalQuotientPresheaf X.𝒪.presheaf).map
          ((Opens.map f.base).op.map i) := sorry

/-- The morphism from the total-quotient presheaf on the target to the pushforward of the
total-quotient presheaf on the source. -/
noncomputable def meromorphicFunctionPresheafMap
    (f : X ⟶ Y) (hf : pullbacksRegularMeromorphicFunctionsDefined f) :
    TopCat.Presheaf.totalQuotientPresheaf Y.𝒪.presheaf ⟶
      (Opens.map f.base).op ⋙
        TopCat.Presheaf.totalQuotientPresheaf X.𝒪.presheaf where
  app V := meromorphicFunctionPresheafMapApp f hf V
  naturality _ _ i := meromorphicFunctionPresheafMap_naturality f hf i

/-- The morphism from meromorphic functions on the target to the pushforward of meromorphic
functions on the source. -/
noncomputable def meromorphicFunctionSheafMap
    (f : X ⟶ Y) (hf : pullbacksRegularMeromorphicFunctionsDefined f) :
    Y.meromorphicFunctionSheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
        X.meromorphicFunctionSheaf :=
  ⟨CategoryTheory.sheafifyLift (Opens.grothendieckTopology Y.toTopCat)
    (meromorphicFunctionPresheafMap f hf ≫
      Functor.whiskerLeft (Opens.map f.base).op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
          (TopCat.Presheaf.totalQuotientPresheaf X.𝒪.presheaf)))
    ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
      X.meromorphicFunctionSheaf).2⟩

/-- The induced map on meromorphic-function sheaves extends the original structure-sheaf map. -/
theorem toMeromorphicFunctionSheafHom_naturality
    (f : X ⟶ Y) (hf : pullbacksRegularMeromorphicFunctionsDefined f) :
    Y.toMeromorphicFunctionSheafHom ≫ meromorphicFunctionSheafMap f hf =
      RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map
          X.toMeromorphicFunctionSheafHom := sorry

/-- A morphism preserving meromorphic denominators induces a morphism between the ringed spaces
whose structure sheaves are the corresponding meromorphic-function sheaves. -/
noncomputable def meromorphicFunctionRingedSpaceHom
    (f : X ⟶ Y) (hf : pullbacksRegularMeromorphicFunctionsDefined f) :
    X.meromorphicFunctionSheaf.toRingedSpace ⟶
      Y.meromorphicFunctionSheaf.toRingedSpace :=
  SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
    { base := f.base
      c := (meromorphicFunctionSheafMap f hf).hom }

end Hom
end AlgebraicGeometry.LocallyRingedSpace
