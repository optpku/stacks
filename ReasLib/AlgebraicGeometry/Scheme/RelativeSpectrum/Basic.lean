/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic

/-!
# The relative-spectrum functor

This leaf defines the functor of points of the relative spectrum of a
quasi-coherent algebra sheaf. Representability, constructions, and base change
are kept in separate leaves.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite
open RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T T' : Scheme.{u}}

/-- A relative-spectrum point over `T` consists of a morphism `T ⟶ S` and an algebra map
from `A` to the pushforward of the structure sheaf of `T`. -/
abbrev relativeSpectrumPair (A : S.QcAlgebraUnder) (T : Scheme.{u}) : Type u :=
  Σ f : T ⟶ S, A.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap f.toShHom)

/-- The map between target algebra sheaves induced by precomposition of a relative-spectrum
point with a scheme morphism. -/
abbrev relativeSpectrumPairTargetMap (f : T ⟶ S) (a : T' ⟶ T) :
    Under.mk (Hom.commRingSheafPushforwardMap f.toShHom) ⟶
      Under.mk (Hom.commRingSheafPushforwardMap (a ≫ f).toShHom) :=
  Under.homMk
    ((TopCat.Sheaf.pushforward CommRingCat.{u} f.1.base).map
      (Hom.commRingSheafPushforwardMap a.toShHom))
    rfl

/-- The action on relative-spectrum points induced by a morphism in `Schemeᵒᵖ`. -/
def relativeSpectrumFunctorMap
    (A : S.QcAlgebraUnder) {X Y : Schemeᵒᵖ} (a : X ⟶ Y) :
    relativeSpectrumPair A (unop X) → relativeSpectrumPair A (unop Y) :=
  fun x ↦
    (⟨unop a ≫ x.1, x.2 ≫ relativeSpectrumPairTargetMap x.1 (unop a)⟩ :
      relativeSpectrumPair A (unop Y))

/-- Pull a relative-spectrum point back along a morphism of schemes. This is the direct-scheme
form of `relativeSpectrumFunctorMap`, avoiding opposite-category bookkeeping in applications. -/
def relativeSpectrumPairPullbackMap
    (A : S.QcAlgebraUnder) {T T' : Scheme.{u}} (a : T' ⟶ T) :
    relativeSpectrumPair A T → relativeSpectrumPair A T' :=
  relativeSpectrumFunctorMap A (op a)

/-- The action on relative-spectrum points preserves identity morphisms. -/
theorem relativeSpectrumFunctor_map_id (A : S.QcAlgebraUnder) (X : Schemeᵒᵖ) :
    relativeSpectrumFunctorMap A (𝟙 X) = id := sorry

/-- The action on relative-spectrum points preserves composition in `Schemeᵒᵖ`. -/
theorem relativeSpectrumFunctor_map_comp (A : S.QcAlgebraUnder) {X Y Z : Schemeᵒᵖ}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    relativeSpectrumFunctorMap A (a ≫ b) =
      relativeSpectrumFunctorMap A b ∘ relativeSpectrumFunctorMap A a := sorry

/-- The contravariant functor of points associated to a quasi-coherent algebra sheaf. -/
def relativeSpectrumFunctor (A : S.QcAlgebraUnder) : Schemeᵒᵖ ⥤ Type u where
  obj T := relativeSpectrumPair A (unop T)
  map a := TypeCat.ofHom (relativeSpectrumFunctorMap A a)
  map_id X := congrArg TypeCat.ofHom (relativeSpectrumFunctor_map_id A X)
  map_comp a b := congrArg TypeCat.ofHom (relativeSpectrumFunctor_map_comp A a b)

/-- Evaluating the relative-spectrum functor on a scheme recovers its explicit pair type. -/
theorem relativeSpectrumFunctor_obj (A : S.QcAlgebraUnder) (T : Scheme.{u}) :
    (relativeSpectrumFunctor A).obj (op T) = relativeSpectrumPair A T := sorry

/-- The algebra map carried by a relative-spectrum point. -/
def relativeSpectrumUniversalMap
    (A : S.QcAlgebraUnder) {X : Scheme.{u}}
    (x : relativeSpectrumPair A X) :
    (QcAlgebraUnder.forget S).obj A ⟶
      Under.mk (Hom.commRingSheafPushforwardMap x.1.toShHom) :=
  x.2

/-- The algebra map carried by a relative-spectrum point whose structural morphism is identified
with a prescribed morphism. -/
def relativeSpectrumUniversalMapOver
    (A : S.QcAlgebraUnder) {X : Scheme.{u}} (π : X ⟶ S)
    (x : relativeSpectrumPair A X)
    (hxπ : x.1 = π) :
    (QcAlgebraUnder.forget S).obj A ⟶
      Under.mk (Hom.commRingSheafPushforwardMap π.toShHom) :=
  match hxπ with
  | rfl => relativeSpectrumUniversalMap A x

end AlgebraicGeometry.Scheme
