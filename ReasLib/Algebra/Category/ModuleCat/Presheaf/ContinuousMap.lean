/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Notation
public import ReasLib.Topology.Sheaves.Ring.Definition

/-!
# Inverse image of presheaves of modules along continuous maps

This module packages the change-of-scalars presentation of inverse image for modules over a
commutative ring presheaf on the source of a continuous map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf TopCat

noncomputable section

universe u

namespace TopCat.Presheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : X.Presheaf CommRingCat.{u})

/-- The inverse-image functor on modules over a commutative ring presheaf on the source of a
continuous map.  It is the composite of extension of scalars along the pullback unit for
`f_* 𝒪` and along the counit `f⁻¹(f_* 𝒪) ⟶ 𝒪`. -/
noncomputable def modulePullback :
    PMod(ringPresheafOfComm ((pushforward CommRingCat f).obj 𝒪)) ⥤
      PMod(ringPresheafOfComm 𝒪) :=
  let η := commRingPresheafPullbackUnit f ((pushforward CommRingCat f).obj 𝒪)
  let ε := commRingPresheafHomOverId
    ((pullbackPushforwardAdjunction CommRingCat f).counit.app 𝒪)
  PresheafOfModules.pullback η ⋙ PresheafOfModules.pullback ε

/-- The direct-image functor right adjoint to `modulePullback`.  It first restricts scalars
along `f⁻¹(f_* 𝒪) ⟶ 𝒪` and then along the pullback unit for `f_* 𝒪`. -/
noncomputable def modulePushforward :
    PMod(ringPresheafOfComm 𝒪) ⥤
      PMod(ringPresheafOfComm ((pushforward CommRingCat f).obj 𝒪)) :=
  let η := commRingPresheafPullbackUnit f ((pushforward CommRingCat f).obj 𝒪)
  let ε := commRingPresheafHomOverId
    ((pullbackPushforwardAdjunction CommRingCat f).counit.app 𝒪)
  PresheafOfModules.pushforward ε ⋙ PresheafOfModules.pushforward η

/-- Inverse image of modules along a continuous map is left adjoint to the named module direct
image functor. -/
noncomputable def modulePullbackAdjunction :
    modulePullback f 𝒪 ⊣ modulePushforward f 𝒪 :=
  let η := commRingPresheafPullbackUnit f ((pushforward CommRingCat f).obj 𝒪)
  let ε := commRingPresheafHomOverId
    ((pullbackPushforwardAdjunction CommRingCat f).counit.app 𝒪)
  (PresheafOfModules.pullbackPushforwardAdjunction η).comp
    (PresheafOfModules.pullbackPushforwardAdjunction ε)

/-- The Hom equivalence exhibiting `modulePullback` as the composite left adjoint of the two
canonical module-pushforward functors. -/
noncomputable def modulePullbackHomEquiv
    (𝒢 : PMod(ringPresheafOfComm ((pushforward CommRingCat f).obj 𝒪)))
    (ℱ : PMod(ringPresheafOfComm 𝒪)) :
    ((modulePullback f 𝒪).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (modulePushforward f 𝒪).obj ℱ) :=
  (modulePullbackAdjunction f 𝒪).homEquiv 𝒢 ℱ

end TopCat.Presheaf
