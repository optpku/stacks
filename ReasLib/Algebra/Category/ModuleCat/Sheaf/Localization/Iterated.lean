module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Iterated localization of module sheaves

The iterated slice category `(C / U) / V` is canonically equivalent to `C / V.left`.
This file lifts that equivalence to module sheaves and records the comparison between
iterated restriction and direct restriction.  The construction is independent of
sheafification hypotheses and applies to sheaves of modules over an arbitrary sheaf of rings.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.Localization.Iterated

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The ring morphism from the twice restricted ring sheaf to the direct-image of the
directly restricted ring sheaf along the forward iterated-slice equivalence. -/
@[stacks 04IX "forward ring morphism for iterated restriction"]
noncomputable abbrev forwardRingHom (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    (R.over U).over V ⟶
      ((Over.iteratedSliceForward V).sheafPushforwardContinuous RingCat.{w}
        ((J.over U).over V) (J.over V.left)).obj (R.over V.left) :=
  𝟙 _

/-- The ring morphism from the directly restricted ring sheaf to the direct-image of the
twice restricted ring sheaf along the backward iterated-slice equivalence. -/
@[stacks 04IX "backward ring morphism for iterated restriction"]
noncomputable abbrev backwardRingHom (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    R.over V.left ⟶
      ((Over.iteratedSliceBackward V).sheafPushforwardContinuous RingCat.{w}
        (J.over V.left) ((J.over U).over V)).obj ((R.over U).over V) :=
  𝟙 _

/-- The counit coherence for the two ring morphisms underlying iterated restriction. -/
@[stacks 04IX "counit coherence for iterated restriction"]
theorem ringCounit (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    Functor.whiskerRight (NatTrans.op (Over.iteratedSliceEquiv V).counit)
        (R.over V.left).obj =
      (backwardRingHom R U V).hom ≫
        (Over.iteratedSliceBackward V).op.whiskerLeft (forwardRingHom R U V).hom := sorry

/-- The unit coherence for the two ring morphisms underlying iterated restriction. -/
@[stacks 04IX "unit coherence for iterated restriction"]
theorem ringUnit (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    (forwardRingHom R U V).hom ≫
          (Over.iteratedSliceForward V).op.whiskerLeft (backwardRingHom R U V).hom ≫
        Functor.whiskerRight (NatTrans.op (Over.iteratedSliceEquiv V).unit)
          ((R.over U).over V).obj =
      𝟙 ((R.over U).over V).obj := sorry

/-- The canonical equivalence between module sheaves on the iterated slice `(C / U) / V`
and module sheaves on the direct slice `C / V.left`. -/
@[stacks 04IX "module-sheaf equivalence for iterated restriction"]
noncomputable def equivalence (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    SheafOfModules.{z} ((R.over U).over V) ≌
      SheafOfModules.{z} (R.over V.left) :=
  (SheafOfModules.pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv V) (forwardRingHom R U V) (backwardRingHom R U V)
    (ringCounit R U V) (ringUnit R U V)).symm

/-- The forward functor of the iterated-restriction equivalence is additive. -/
@[stacks 04IX "additivity of the iterated-slice equivalence"]
noncomputable instance equivalenceFunctor_additive
    (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    (equivalence.{u, v, w, z} R U V).functor.Additive := sorry

/-- The inverse functor of the iterated-restriction equivalence is additive. -/
@[stacks 04IX "additivity of the inverse iterated-slice equivalence"]
noncomputable instance equivalenceInverse_additive
    (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    (equivalence.{u, v, w, z} R U V).inverse.Additive := sorry

/-- Restriction first to `U` and then to an object `V : C / U`. -/
@[stacks 04IX "iterated restriction functor"]
noncomputable abbrev functor (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    SheafOfModules.{z} R ⥤ SheafOfModules.{z} ((R.over U).over V) :=
  SheafOfModules.Localization.restriction R U ⋙
    SheafOfModules.Localization.restriction (R.over U) V

/-- Restricting directly to `V.left` and applying the inverse iterated-slice equivalence
agrees with restricting first to `U` and then to `V : C / U`. -/
@[stacks 04IX "factorization of iterated restriction"]
noncomputable def restrictionFactorIso (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    functor.{u, v, w, z} R U V ≅
      (SheafOfModules.Localization.restriction R V.left :
          SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over V.left)) ⋙
        (equivalence.{u, v, w, z} R U V).inverse :=
  SheafOfModules.pushforwardComp
      (restrictionRingHom (R.over U) V) (restrictionRingHom R U) ≪≫
    (SheafOfModules.pushforwardComp
      (forwardRingHom R U V) (restrictionRingHom R V.left)).symm

/-- Restricting first to `U` and then to `V : C / U`, followed by the canonical
iterated-slice equivalence, is naturally isomorphic to restricting directly to `V.left`. -/
@[stacks 04IX "comparison of iterated and direct restriction"]
noncomputable def restrictionIso (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    functor.{u, v, w, z} R U V ⋙ (equivalence.{u, v, w, z} R U V).functor ≅
      (SheafOfModules.Localization.restriction R V.left :
        SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over V.left)) :=
  Functor.isoWhiskerRight (restrictionFactorIso.{u, v, w, z} R U V)
      (equivalence.{u, v, w, z} R U V).functor ≪≫
    Functor.associator
      (SheafOfModules.Localization.restriction R V.left :
        SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over V.left))
      (equivalence.{u, v, w, z} R U V).inverse (equivalence.{u, v, w, z} R U V).functor ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.Localization.restriction R V.left :
        SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over V.left))
      (equivalence.{u, v, w, z} R U V).counitIso ≪≫
    Functor.rightUnitor
      (SheafOfModules.Localization.restriction R V.left :
        SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over V.left))

section AdditiveInstances

variable (R : Sheaf J RingCat.{w}) (U : C) (V : Over U)

#synth (equivalence.{u, v, w, z} R U V).functor.Additive
#synth (equivalence.{u, v, w, z} R U V).inverse.Additive

end AdditiveInstances

end SheafOfModules.Localization.Iterated
