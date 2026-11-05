module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.Algebra.Category.Ring.Sheaf

/-!
# Ring (pre)sheaves on topological spaces

This file contains the `TopCat`-specific presentations of morphisms of ring (pre)sheaves used
by the module (pre)sheaf pullback and pushforward APIs.  The underlying conversion from
commutative rings to rings remains owned by `CategoryTheory.Presheaf` and
`CategoryTheory.Sheaf`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe w u

noncomputable section

namespace TopCat.Presheaf

variable {X : TopCat.{w}}

/-- A morphism of ring presheaves on one space, in the identity-site form used by change and
restriction of scalars for presheaves of modules. -/
abbrev ringPresheafHomOverId {𝒪₁ 𝒪₂ : X.Presheaf RingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂) :
    𝒪₁ ⟶ (𝟭 (TopologicalSpace.Opens X)).op ⋙ 𝒪₂ :=
  p ≫ 𝒪₂.leftUnitor.inv

/-- A same-space morphism of commutative-ring presheaves, viewed as the identity-site morphism
of underlying ring presheaves used by change and restriction of scalars. -/
abbrev commRingPresheafHomOverId
    {𝒪₁ 𝒪₂ : X.Presheaf CommRingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂) :
    CategoryTheory.Presheaf.ringPresheafOfComm 𝒪₁ ⟶
      (𝟭 (TopologicalSpace.Opens X)).op ⋙
        CategoryTheory.Presheaf.ringPresheafOfComm 𝒪₂ :=
  ringPresheafHomOverId (CategoryTheory.Presheaf.ringPresheafOfCommMap p)

/-- The pullback adjunction unit for a commutative-ring presheaf, viewed as a morphism of
underlying possibly noncommutative ring presheaves. -/
abbrev commRingPresheafPullbackUnit {X' Y' : TopCat.{u}}
    (f : X' ⟶ Y') (𝒪 : Y'.Presheaf CommRingCat.{u}) :
    CategoryTheory.Presheaf.ringPresheafOfComm 𝒪 ⟶
      (TopologicalSpace.Opens.map f).op ⋙
        CategoryTheory.Presheaf.ringPresheafOfComm
          ((pullback CommRingCat f).obj 𝒪) :=
  CategoryTheory.Presheaf.ringPresheafOfCommMap
    ((pullbackPushforwardAdjunction CommRingCat f).unit.app 𝒪)

/-- Along an open map, forgetting commutativity commutes with pullback of presheaves.

For a general continuous map, presheaf pullback is a left Kan extension and this comparison need
not be available from the forgetful functor alone.  Openness identifies both pullbacks with
precomposition, yielding the displayed canonical isomorphism. -/
noncomputable def ringPresheafOfCommPullbackIso
    {X' Y' : TopCat.{u}} (f : X' ⟶ Y') (hf : IsOpenMap f)
    (𝒪 : Y'.Presheaf CommRingCat.{u}) :
    CategoryTheory.Presheaf.ringPresheafOfComm
        ((pullback CommRingCat f).obj 𝒪) ≅
      (pullback RingCat f).obj
        (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪) :=
  Functor.isoWhiskerRight (hf.pullbackObjIso 𝒪)
      (forget₂ CommRingCat RingCat) ≪≫
    Functor.associator _ _ _ ≪≫
      (hf.pullbackObjIso
        (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪)).symm

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {X : TopCat.{w}}

/-- The underlying possibly noncommutative ring sheaf of a sheaf of commutative rings on a
topological space. -/
abbrev ringSheafOfComm (𝒪 : X.Sheaf CommRingCat.{u}) [UnivLE.{w, u}] :
    X.Sheaf RingCat.{u} :=
  CategoryTheory.Sheaf.ringSheafOfComm (J := Opens.grothendieckTopology X) 𝒪

/-- The morphism of underlying ring sheaves induced by a morphism of commutative-ring sheaves on
a topological space. -/
abbrev ringSheafOfCommMap {𝒪₁ 𝒪₂ : X.Sheaf CommRingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂)
    [UnivLE.{w, u}] :
    ringSheafOfComm 𝒪₁ ⟶ ringSheafOfComm 𝒪₂ :=
  CategoryTheory.Sheaf.ringSheafOfCommMap (J := Opens.grothendieckTopology X) p

/-- View a same-space morphism of ring sheaves in the identity-pushforward form expected by
module-sheaf change of scalars. -/
abbrev ringSheafHomOverId {𝒪₁ 𝒪₂ : X.Sheaf RingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂) :
    𝒪₁ ⟶
      ((𝟭 (Opens X)).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).obj 𝒪₂ :=
  p

/-- View a same-space morphism of commutative-ring sheaves as the underlying ring-sheaf
morphism used by change and restriction of scalars. -/
abbrev commRingSheafHomOverId {𝒪₁ 𝒪₂ : X.Sheaf CommRingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂)
    [UnivLE.{w, u}] :
    ringSheafOfComm 𝒪₁ ⟶
      ((𝟭 (Opens X)).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).obj
          (ringSheafOfComm 𝒪₂) :=
  ringSheafHomOverId (ringSheafOfCommMap p)

/-- The identity comparison from the underlying ring sheaf of a direct-image commutative-ring
sheaf to the direct image of its underlying ring sheaf. -/
noncomputable abbrev commRingSheafPushforwardId
    [UnivLE.{w, u}] {Y : TopCat.{w}} (f : X ⟶ Y) (𝒪 : X.Sheaf CommRingCat.{u}) :
    ringSheafOfComm ((Sheaf.pushforward CommRingCat.{u} f).obj 𝒪) ⟶
      ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
          (ringSheafOfComm 𝒪) :=
  𝟙 _

/-- The pullback adjunction unit for a commutative-ring sheaf, viewed as a morphism of underlying
possibly noncommutative ring sheaves. -/
noncomputable abbrev commRingSheafPullbackUnit {X' Y' : TopCat.{u}}
    (f : X' ⟶ Y') (𝒪 : Y'.Sheaf CommRingCat.{u}) :
    ringSheafOfComm.{u, u} 𝒪 ⟶
      ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology Y') (Opens.grothendieckTopology X')).obj
          (ringSheafOfComm.{u, u}
            ((Sheaf.pullback CommRingCat.{u} f).obj 𝒪)) :=
  ringSheafOfCommMap.{u, u}
    ((Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app 𝒪)

end TopCat.Sheaf
