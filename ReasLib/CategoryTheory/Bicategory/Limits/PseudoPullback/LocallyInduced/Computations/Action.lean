/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Computations.Cone
import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Pseudofunctor.Computations.Map

/-!
# Action computations for locally induced pseudopullback cones

This leaf exposes the object, morphism, and `2`-morphism actions of the locally induced
forgetful cone pseudofunctor, including all three readable comparison components.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA uB vB wB

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {A : Type uA} {B : Type uB} [Bicategory.{wB, vB} B]
variable {baseObj : A → B} {Q : Bicategory.HomProperty baseObj} [Q.IsMultiplicative]
variable {x y z : Bicategory.LocallyInducedBicategory B baseObj Q}
variable {f : x ⟶ z} {g : y ⟶ z}

/-- The object action of the locally induced forgetful cone pseudofunctor is
`forgetLocallyInduced`. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.obj
    (P : PseudoPullbackCone f g) :
    (forgetLocallyInduced.pseudofunctor f g).obj P =
      P.forgetLocallyInduced := sorry

/-- The morphism action of the locally induced forgetful cone pseudofunctor is the canonical
readable mapped-cone morphism. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.map
    {P R : PseudoPullbackCone f g} (u : P ⟶ R) :
    (forgetLocallyInduced.pseudofunctor f g).map u =
      Pseudofunctor.mapPseudoPullbackCone.map
        ((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor) u := sorry

/-- The `2`-morphism action of the locally induced forgetful cone pseudofunctor is the canonical
readable mapped-cone `2`-morphism. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.map₂
    {P R : PseudoPullbackCone f g} {u v : P ⟶ R} (η : u ⟶ v) :
    (forgetLocallyInduced.pseudofunctor f g).map₂ η =
      Pseudofunctor.mapPseudoPullbackCone.map₂
        ((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor) η := sorry

/-- Forgetting a readable cone morphism exposes the ambient apex map of the selected original
apex map. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.map.apex
    {P R : PseudoPullbackCone f g} (u : P ⟶ R) :
    PseudoPullbackCone.map
        ((forgetLocallyInduced.pseudofunctor f g).map u) =
      (PseudoPullbackCone.map u).obj := sorry

/-- Forgetting a readable cone `2`-morphism exposes the ambient cell of the selected original
apex cell. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.map₂.apex
    {P R : PseudoPullbackCone f g} {u v : P ⟶ R} (η : u ⟶ v) :
    PseudoPullbackCone.map₂
        ((forgetLocallyInduced.pseudofunctor f g).map₂ η) =
      (PseudoPullbackCone.map₂ η).hom := sorry

/-- The comparison modification of a forgotten readable cone morphism is the canonical mapped
comparison for the locally induced forgetful pseudofunctor. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.map.fac
    {P R : PseudoPullbackCone f g} (u : P ⟶ R) :
    PseudoPullbackCone.fac
        ((forgetLocallyInduced.pseudofunctor f g).map u) =
      Pseudofunctor.mapPseudoPullbackCone.fac
        ((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor) u := sorry

/-- Forgetting a readable cone morphism exposes the ambient cell of its selected left-leg
comparison. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.map.fstFac
    {P R : PseudoPullbackCone f g} (u : P ⟶ R) :
    PseudoPullbackCone.fstFac
        ((forgetLocallyInduced.pseudofunctor f g).map u) =
      (PseudoPullbackCone.fstFac u).hom := sorry

/-- Forgetting a readable cone morphism exposes the ambient cell of its selected right-leg
comparison. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.map.sndFac
    {P R : PseudoPullbackCone f g} (u : P ⟶ R) :
    PseudoPullbackCone.sndFac
        ((forgetLocallyInduced.pseudofunctor f g).map u) =
      (PseudoPullbackCone.sndFac u).hom := sorry

/-- Forgetting a readable cone morphism exposes the ambient cell of its selected central
comparison. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.map.baseFac
    {P R : PseudoPullbackCone f g} (u : P ⟶ R) :
    PseudoPullbackCone.baseFac
        ((forgetLocallyInduced.pseudofunctor f g).map u) =
      (PseudoPullbackCone.baseFac u).hom := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
