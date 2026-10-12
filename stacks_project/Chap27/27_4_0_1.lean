/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Basic
import StacksCheckRecall

/-!
# 27.4.0.1 compatibility entry point

The relative-spectrum functor and its pointwise computation API are neutral
scheme infrastructure owned by ReasLib.
-/

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry.RingedSpace

universe u

/- 27.4.0.1: the functor of points associated to a quasi-coherent `𝒪_S`-algebra. -/
@[stacks 01LR] #check (AlgebraicGeometry.Scheme.relativeSpectrumFunctor :
  {S : AlgebraicGeometry.Scheme.{u}} → S.QcAlgebraUnder →
    AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.Scheme.relativeSpectrumPair :
  {S : AlgebraicGeometry.Scheme.{u}} →
    S.QcAlgebraUnder → AlgebraicGeometry.Scheme.{u} → Type u)

#check (AlgebraicGeometry.Scheme.relativeSpectrumPairTargetMap :
  {S T T' : AlgebraicGeometry.Scheme.{u}} → (f : T ⟶ S) → (a : T' ⟶ T) →
    Under.mk (Hom.commRingSheafPushforwardMap f.toShHom) ⟶
      Under.mk (Hom.commRingSheafPushforwardMap (a ≫ f).toShHom))

#check (AlgebraicGeometry.Scheme.relativeSpectrumFunctorMap :
  {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
    {X Y : AlgebraicGeometry.Scheme.{u}ᵒᵖ} → (a : X ⟶ Y) →
      AlgebraicGeometry.Scheme.relativeSpectrumPair A (unop X) →
        AlgebraicGeometry.Scheme.relativeSpectrumPair A (unop Y))

#check (AlgebraicGeometry.Scheme.relativeSpectrumPairPullbackMap :
  {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
    {T T' : AlgebraicGeometry.Scheme.{u}} → (a : T' ⟶ T) →
      AlgebraicGeometry.Scheme.relativeSpectrumPair A T →
        AlgebraicGeometry.Scheme.relativeSpectrumPair A T')

#check (AlgebraicGeometry.Scheme.relativeSpectrumFunctor_map_id :
  {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
    (X : AlgebraicGeometry.Scheme.{u}ᵒᵖ) →
      AlgebraicGeometry.Scheme.relativeSpectrumFunctorMap A (𝟙 X) = id)

#check (AlgebraicGeometry.Scheme.relativeSpectrumFunctor_map_comp :
  {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
    {X Y Z : AlgebraicGeometry.Scheme.{u}ᵒᵖ} → (a : X ⟶ Y) → (b : Y ⟶ Z) →
      AlgebraicGeometry.Scheme.relativeSpectrumFunctorMap A (a ≫ b) =
        AlgebraicGeometry.Scheme.relativeSpectrumFunctorMap A b ∘
          AlgebraicGeometry.Scheme.relativeSpectrumFunctorMap A a)

#check (AlgebraicGeometry.Scheme.relativeSpectrumFunctor_obj :
  {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
    (T : AlgebraicGeometry.Scheme.{u}) →
      (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).obj (op T) =
        (Σ f : T ⟶ S,
          A.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap f.toShHom)))

#check (AlgebraicGeometry.Scheme.relativeSpectrumUniversalMap :
  {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
    {X : AlgebraicGeometry.Scheme.{u}} →
      (x : AlgebraicGeometry.Scheme.relativeSpectrumPair A X) →
        (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj A ⟶
          Under.mk (Hom.commRingSheafPushforwardMap x.1.toShHom))

#check (AlgebraicGeometry.Scheme.relativeSpectrumUniversalMapOver :
  {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
    {X : AlgebraicGeometry.Scheme.{u}} → (π : X ⟶ S) →
      (x : AlgebraicGeometry.Scheme.relativeSpectrumPair A X) → (hxπ : x.1 = π) →
        (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj A ⟶
          Under.mk (Hom.commRingSheafPushforwardMap π.toShHom))
