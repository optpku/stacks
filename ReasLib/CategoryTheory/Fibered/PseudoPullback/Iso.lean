/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}

namespace PseudoPullback

/-- Compatibility of inverse component isomorphisms follows from compatibility of their forward
components. -/
theorem mkIso.inv.comm
    {P Q : (PseudoPullback F G).obj}
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    CommSq (F.toFunctor.map fst.inv) (comparison Q)
      (comparison P) (G.toFunctor.map snd.inv) := sorry

/-- The morphisms assembled from mutually inverse base and component isomorphisms compose to the
identity on the source pseudo-pullback object. -/
theorem mkIso.hom.inv_id
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    PseudoPullback.Hom.mk base.hom fst.hom hom_fst snd.hom hom_snd w ≫
        PseudoPullback.Hom.mk base.inv fst.inv
          (Functor.IsHomLift.inv_lift_inv_of (p := X.p) base fst hom_fst)
          snd.inv (Functor.IsHomLift.inv_lift_inv_of (p := Y.p) base snd hom_snd)
          (mkIso.inv.comm fst snd w) =
      𝟙 P := sorry

/-- The morphisms assembled from mutually inverse base and component isomorphisms compose to the
identity on the target pseudo-pullback object. -/
theorem mkIso.inv.hom_id
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    PseudoPullback.Hom.mk base.inv fst.inv
          (Functor.IsHomLift.inv_lift_inv_of (p := X.p) base fst hom_fst)
          snd.inv (Functor.IsHomLift.inv_lift_inv_of (p := Y.p) base snd hom_snd)
          (mkIso.inv.comm fst snd w) ≫
        PseudoPullback.Hom.mk base.hom fst.hom hom_fst snd.hom hom_snd w =
      𝟙 Q := sorry

/-- Construct an isomorphism of pseudo-pullback objects from compatible isomorphisms of their
base, first, and second components. Only compatibility of the forward components must be
supplied; inverse compatibility is automatic. -/
@[stacks 0040 "isomorphism of based pseudo-pullback objects"]
noncomputable def mkIso
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    P ≅ Q where
  hom := PseudoPullback.Hom.mk base.hom fst.hom hom_fst snd.hom hom_snd w
  inv := PseudoPullback.Hom.mk base.inv fst.inv
    (Functor.IsHomLift.inv_lift_inv_of (p := X.p) base fst hom_fst)
    snd.inv (Functor.IsHomLift.inv_lift_inv_of (p := Y.p) base snd hom_snd)
    (mkIso.inv.comm fst snd w)
  hom_inv_id := mkIso.hom.inv_id base fst snd hom_fst hom_snd w
  inv_hom_id := mkIso.inv.hom_id base fst snd hom_fst hom_snd w

/-- The base component of the forward morphism of `mkIso` is the supplied base isomorphism. -/
@[simp]
theorem mkIso.hom.baseMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    baseMap (mkIso base fst snd hom_fst hom_snd w).hom =
      base.hom := sorry

/-- The first component of the forward morphism of `mkIso` is the supplied first-component
isomorphism. -/
@[simp]
theorem mkIso.hom.fstMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    fstMap (mkIso base fst snd hom_fst hom_snd w).hom =
      fst.hom := sorry

/-- The second component of the forward morphism of `mkIso` is the supplied second-component
isomorphism. -/
@[simp]
theorem mkIso.hom.sndMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    sndMap (mkIso base fst snd hom_fst hom_snd w).hom =
      snd.hom := sorry

/-- The base component of the inverse morphism of `mkIso` is the inverse supplied base
isomorphism. -/
@[simp]
theorem mkIso.inv.baseMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    baseMap (mkIso base fst snd hom_fst hom_snd w).inv =
      base.inv := sorry

/-- The first component of the inverse morphism of `mkIso` is the inverse supplied
first-component isomorphism. -/
@[simp]
theorem mkIso.inv.fstMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    fstMap (mkIso base fst snd hom_fst hom_snd w).inv =
      fst.inv := sorry

/-- The second component of the inverse morphism of `mkIso` is the inverse supplied
second-component isomorphism. -/
@[simp]
theorem mkIso.inv.sndMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ≅ baseObj Q)
    (fst : fstObj P ≅ fstObj Q)
    (snd : sndObj P ≅ sndObj Q)
    (hom_fst : X.p.IsHomLift base.hom fst.hom)
    (hom_snd : Y.p.IsHomLift base.hom snd.hom)
    (w : CommSq (F.toFunctor.map fst.hom) (comparison P)
      (comparison Q) (G.toFunctor.map snd.hom)) :
    sndMap (mkIso base fst snd hom_fst hom_snd w).inv =
      snd.inv := sorry

end PseudoPullback
end BasedCategory
end CategoryTheory
