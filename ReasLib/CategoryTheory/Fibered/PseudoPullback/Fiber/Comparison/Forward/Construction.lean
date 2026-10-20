/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the forward fibre comparison

This leaf constructs the functor from the actual fibre of a based pseudo-pullback to the
categorical pullback of the two corresponding fibres. Object and morphism readouts are provided
by the separate `Forward.Computations` leaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback

universe u v uX uY uS vX vY vS

namespace CategoryTheory
namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

noncomputable section

namespace PseudoPullback

namespace Fiber

section ComparisonForwardImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- An object of the fibre of the bundled pseudo-pullback over U already stores an object of
the pullback of the fibre categories over U. -/
private def toPullbackObj
    (U : C) (P : Functor.Fiber (PseudoPullback F G).p U) :
    (F.fiberFunctor U) ⊡ (G.fiberFunctor U) :=
  P.2 ▸ PseudoPullback.fiberObj P.1

/-- Transporting the stored fibrewise pullback to U preserves its first underlying object. -/
@[simp]
private theorem toPullbackObj_fst_val
    (U : C) (P : Functor.Fiber (PseudoPullback F G).p U) :
    (toPullbackObj F G U P).fst.1 =
      PseudoPullback.fstObj P.1 := sorry

/-- Transporting the stored fibrewise pullback to U preserves its second underlying object. -/
@[simp]
private theorem toPullbackObj_snd_val
    (U : C) (P : Functor.Fiber (PseudoPullback F G).p U) :
    (toPullbackObj F G U P).snd.1 =
      PseudoPullback.sndObj P.1 := sorry

/-- The transported first-component map underlying a morphism between pullback fibres. -/
private def toPullbackFstMap
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) :
    (toPullbackObj F G U P).fst.1 ⟶
      (toPullbackObj F G U Q).fst.1 :=
  eqToHom (toPullbackObj_fst_val F G U P) ≫
    PseudoPullback.fstMap φ.1 ≫
      eqToHom (toPullbackObj_fst_val F G U Q).symm

/-- The transported second-component map underlying a morphism between pullback fibres. -/
private def toPullbackSndMap
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) :
    (toPullbackObj F G U P).snd.1 ⟶
      (toPullbackObj F G U Q).snd.1 :=
  eqToHom (toPullbackObj_snd_val F G U P) ≫
    PseudoPullback.sndMap φ.1 ≫
      eqToHom (toPullbackObj_snd_val F G U Q).symm

/-- The transported first component lies over the identity of U. -/
private theorem toPullbackFstIsHomLift
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) :
    X.p.IsHomLift (𝟙 U) (toPullbackFstMap F G φ) := sorry

/-- The transported second component lies over the identity of U. -/
private theorem toPullbackSndIsHomLift
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) :
    Y.p.IsHomLift (𝟙 U) (toPullbackSndMap F G φ) := sorry

/-- The first component of the inverse morphism assembly. -/
private def toPullbackFst
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) :
    (toPullbackObj F G U P).fst ⟶
      (toPullbackObj F G U Q).fst :=
  ⟨toPullbackFstMap F G φ, toPullbackFstIsHomLift F G φ⟩

/-- The second component of the inverse morphism assembly. -/
private def toPullbackSnd
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) :
    (toPullbackObj F G U P).snd ⟶
      (toPullbackObj F G U Q).snd :=
  ⟨toPullbackSndMap F G φ, toPullbackSndIsHomLift F G φ⟩

/-- The two inverse component maps satisfy the categorical-pullback compatibility equation. -/
private theorem toPullbackMapComm
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) :
    (F.fiberFunctor U).map (toPullbackFst F G φ) ≫
        (toPullbackObj F G U Q).iso.hom =
      (toPullbackObj F G U P).iso.hom ≫
        (G.fiberFunctor U).map (toPullbackSnd F G φ) := sorry

/-- The inverse morphism assembled in the categorical pullback of fibres. -/
private def toPullbackMap
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) :
    toPullbackObj F G U P ⟶
      toPullbackObj F G U Q :=
  { fst := toPullbackFst F G φ
    snd := toPullbackSnd F G φ
    w := toPullbackMapComm F G φ }

/-- The inverse map assembly preserves identities. -/
private theorem toPullbackMapId
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    toPullbackMap F G (𝟙 P) =
      𝟙 (toPullbackObj F G U P) := sorry

/-- The inverse map assembly preserves composition. -/
private theorem toPullbackMapComp
    {U : C} {P Q R : Functor.Fiber (PseudoPullback F G).p U}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    toPullbackMap F G (φ ≫ ψ) =
      toPullbackMap F G φ ≫ toPullbackMap F G ψ := sorry

end Implementation

/-- Forgetting the redundant outer fibre equality gives the canonical comparison from the
actual pseudo-pullback fibre to the pullback model of the two source fibres. -/
@[stacks 02XI "fibre comparison for a based pseudo-pullback"]
def comparison
    (U : C) :
    Functor.Fiber (PseudoPullback F G).p U ⥤
      ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) where
  obj := Implementation.toPullbackObj F G U
  map := Implementation.toPullbackMap F G
  map_id := Implementation.toPullbackMapId F G
  map_comp := Implementation.toPullbackMapComp F G

end ComparisonForwardImplementation

end Fiber

end PseudoPullback
end

end BasedCategory
end CategoryTheory
