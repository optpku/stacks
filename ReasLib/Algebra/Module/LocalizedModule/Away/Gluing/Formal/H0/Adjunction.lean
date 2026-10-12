/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.H0.OfModule
import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical formal-gluing adjunction

The canonical formal-gluing functor is left adjoint to degree-zero sections.
The counit is built from the two literal projections of the defining
degree-zero kernel: its global projection is transposed across extension and
restriction of scalars, while each source-local projection is localized.

The categorical facade uses `FormalGluing.{u, w, w}`: the indexing type and
the gluing-module carriers lie in `Type w`, while degree-zero sections lie in
`ModuleCat.{max u w} R`.

@stack 0H77
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u w

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type w} {φ : R →+* S} {f : ι → R}

/-- The projection from degree-zero sections to the restricted global
target-ring module. -/
@[stacks 0H77 "formal gluing degree-zero global projection"]
noncomputable def h0GlobalProjection (X : FormalGluing.{u, w, w} φ f) :
    X.h0Object ⟶ (ModuleCat.restrictScalars φ).obj X.globalModule :=
  ModuleCat.ofHom
    (X := X.h0Object)
    (Y := (ModuleCat.restrictScalars φ).obj X.globalModule) <|
    (LinearMap.fst R
      ((ModuleCat.restrictScalars φ).obj X.globalModule)
      X.sourceGluing.gluedModule).comp X.h0Module.subtype

/-- The projection from degree-zero sections to the module of compatible
source-local sections. -/
@[stacks 0H77 "formal gluing degree-zero source projection"]
noncomputable def h0GluedProjection (X : FormalGluing.{u, w, w} φ f) :
    X.h0Object ⟶ ModuleCat.of R X.sourceGluing.gluedModule :=
  ModuleCat.ofHom <|
    (LinearMap.snd R
      ((ModuleCat.restrictScalars φ).obj X.globalModule)
      X.sourceGluing.gluedModule).comp X.h0Module.subtype

/-- The global component of the counit `Can(H⁰(X)) ⟶ X`, obtained by
transposing the global degree-zero projection. -/
@[stacks 0H77 "formal gluing adjunction counit global map"]
noncomputable def h0CounitGlobalMap (X : FormalGluing.{u, w, w} φ f) :
    (ModuleCat.extendScalars φ).obj X.h0Object ⟶ X.globalModule :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv
    X.h0Object X.globalModule).symm (h0GlobalProjection X)

/-- The `i`-th source-local component of the counit `Can(H⁰(X)) ⟶ X`.
It localizes the source projection and then evaluates the compatible family
at `i`. -/
@[stacks 0H77 "formal gluing adjunction counit local map"]
noncomputable def h0CounitLocalMap (X : FormalGluing.{u, w, w} φ f)
    (i : ι) :
    (Gluing.ofModule f X.h0Object).localModule i ⟶
      X.sourceGluing.localModule i :=
  ModuleCat.ofHom <|
    (X.sourceGluing.localizedProjection i).comp
      (LocalizedModule.map (Submonoid.powers (f i))
        (h0GluedProjection X).hom)

/-- The localized counit components commute with the source-gluing overlap
isomorphisms. -/
@[stacks 0H77 "formal gluing adjunction counit overlap compatibility"]
theorem h0CounitSourceMap_comm (X : FormalGluing.{u, w, w} φ f) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (f i * f j))
          ((h0CounitLocalMap X i).hom.restrictScalars R))
        ((Gluing.ofModule f X.h0Object).overlapIso i j).hom
        (X.sourceGluing.overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (f i * f j))
          ((h0CounitLocalMap X j).hom.restrictScalars R)) := sorry

/-- The source-gluing component of the counit `Can(H⁰(X)) ⟶ X`. -/
@[stacks 0H77 "formal gluing adjunction counit source map"]
noncomputable def h0CounitSourceMap (X : FormalGluing.{u, w, w} φ f) :
    Gluing.ofModule f X.h0Object ⟶ X.sourceGluing where
  hom i := h0CounitLocalMap X i
  comm := h0CounitSourceMap_comm X

/-- The global and source components of the counit commute with the defining
formal-gluing comparison. -/
@[stacks 0H77 "formal gluing adjunction counit comparison"]
theorem h0CounitHom_comm (X : FormalGluing.{u, w, w} φ f) :
    CommSq
      (Gluing.ofModuleMap (fun i ↦ φ (f i)) (h0CounitGlobalMap X))
      (Gluing.ofModuleBaseChangeIso φ f X.h0Object).hom
      X.comparisonIso.hom
      (Gluing.baseChangeMap φ (h0CounitSourceMap X)) := sorry

/-- The counit morphism `Can(H⁰(X)) ⟶ X` of the canonical formal-gluing
adjunction. -/
@[stacks 0H77 "formal gluing adjunction counit morphism"]
noncomputable def h0CounitHom (X : FormalGluing.{u, w, w} φ f) :
    ofModule φ f X.h0Object ⟶ X where
  globalMap := h0CounitGlobalMap X
  sourceMap := h0CounitSourceMap X
  comm := h0CounitHom_comm X

/-- The formal-gluing counit morphisms are natural. -/
@[stacks 0H77 "formal gluing adjunction counit naturality"]
theorem h0Counit_naturality {X Y : FormalGluing.{u, w, w} φ f}
    (α : X ⟶ Y) :
    (h0Functor.{u, w, w} (φ := φ) (f := f) ⋙
      ofModuleFunctor.{u, w, w} φ f).map α ≫
        h0CounitHom Y =
      h0CounitHom X ≫ α := sorry

/-- The counit natural transformation `Can ⋙ H⁰ ⟶ 𝟭` of canonical formal
gluing. -/
@[stacks 0H77 "formal gluing adjunction counit transformation"]
noncomputable def h0CounitNatTrans :
    h0Functor.{u, w, w} (φ := φ) (f := f) ⋙
        ofModuleFunctor.{u, w, w} φ f ⟶
      𝟭 (FormalGluing.{u, w, w} φ f) where
  app X := h0CounitHom X
  naturality := fun _ _ α ↦ h0Counit_naturality α

/-- The degree-zero unit, viewed directly as a transformation
`𝟭 ⟶ Can ⋙ H⁰`. -/
@[stacks 0H77 "formal gluing adjunction unit transformation"]
noncomputable def h0AdjunctionUnit :
    𝟭 (ModuleCat.{max u w} R) ⟶
      ofModuleFunctor.{u, w, w} φ f ⋙
        h0Functor.{u, w, w} (φ := φ) (f := f) :=
  h0UnitNatTrans φ f ≫ eqToHom (h0OfModuleFunctor_eq_comp φ f)

set_option maxRecDepth 2048 in
/-- The component of the adjunction unit is the explicit degree-zero unit
map, independently of the functor-equality transport used to package it. -/
@[stacks 0H77 "formal gluing adjunction unit component"]
theorem h0AdjunctionUnit_app (M : ModuleCat.{max u w} R) :
    (h0AdjunctionUnit (φ := φ) (f := f)).app M =
      h0UnitHom φ f M := sorry

/-- The unit followed by the counit is the identity on the canonical
formal-gluing functor. -/
@[stacks 0H77 "formal gluing adjunction left triangle"]
theorem h0Adjunction_left_triangle :
    Functor.whiskerRight (h0AdjunctionUnit (φ := φ) (f := f))
        (ofModuleFunctor.{u, w, w} φ f) ≫
      ((ofModuleFunctor.{u, w, w} φ f).associator
          (h0Functor.{u, w, w} (φ := φ) (f := f))
          (ofModuleFunctor.{u, w, w} φ f)).hom ≫
      (ofModuleFunctor.{u, w, w} φ f).whiskerLeft
        (h0CounitNatTrans (φ := φ) (f := f)) =
      𝟙 ((𝟭 (ModuleCat.{max u w} R)).comp
        (ofModuleFunctor.{u, w, w} φ f)) := sorry

set_option maxRecDepth 2048 in
/-- The counit after the unit is the identity on the degree-zero functor. -/
@[stacks 0H77 "formal gluing adjunction right triangle"]
theorem h0Adjunction_right_triangle :
    (h0Functor.{u, w, w} (φ := φ) (f := f)).whiskerLeft
        (h0AdjunctionUnit (φ := φ) (f := f)) ≫
      ((h0Functor.{u, w, w} (φ := φ) (f := f)).associator
          (ofModuleFunctor.{u, w, w} φ f)
          (h0Functor.{u, w, w} (φ := φ) (f := f))).inv ≫
      Functor.whiskerRight (h0CounitNatTrans (φ := φ) (f := f))
        (h0Functor.{u, w, w} (φ := φ) (f := f)) =
      𝟙 (h0Functor.{u, w, w} (φ := φ) (f := f) ⋙
        𝟭 (ModuleCat.{max u w} R)) := sorry

/-- The explicit unit and counit, together with their triangle identities. -/
@[stacks 0H77 "formal gluing adjunction unit-counit core"]
noncomputable def h0AdjunctionCore :
    Adjunction.CoreUnitCounit
      (ofModuleFunctor.{u, w, w} φ f)
      (h0Functor.{u, w, w} (φ := φ) (f := f)) where
  unit := h0AdjunctionUnit
  counit := h0CounitNatTrans
  left_triangle := h0Adjunction_left_triangle
  right_triangle := h0Adjunction_right_triangle

/-- The canonical formal-gluing functor is left adjoint to degree-zero
sections. -/
@[stacks 0H77 "canonical formal gluing adjunction"]
noncomputable def h0Adjunction :
    ofModuleFunctor.{u, w, w} φ f ⊣
      h0Functor.{u, w, w} (φ := φ) (f := f) :=
  Adjunction.mkOfUnitCounit h0AdjunctionCore

end LocalizedModule.Away.FormalGluing
