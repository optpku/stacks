/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.FGModuleCat.ChangeOfRings
public import ReasLib.RingTheory.Ideal.Principal
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite modules in single-element formal gluing

Extension of scalars restricts to finitely generated modules.  For the
principal-adic completion of a Noetherian ring, this restriction packages the
completion and localization components into the finite-module pullback and is
an equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {R : Type u} [CommRing R] (f : R)

/-- The completion component of the formal-gluing datum of a finitely
generated `R`-module is finite over the `f`-adic completion. -/
@[stacks 05ET "finite completion component"]
theorem principalAdicFormalGlueingSingleFunctor_fst_finite
    (M : FGModuleCat.{u} R) :
    Module.Finite (principalAdicCompletion f)
      (((LocalizedModule.Away.FormalGluing.Single.functor
        (algebraMap R (principalAdicCompletion f)) f).obj M.obj).fst) := sorry

/-- The localization component of the formal-gluing datum of a finitely
generated `R`-module is finite over `R_f`. -/
@[stacks 05ET "finite localization component"]
theorem principalAdicFormalGlueingSingleFunctor_snd_finite
    (M : FGModuleCat.{u} R) :
    Module.Finite (Localization.Away f)
      (((LocalizedModule.Away.FormalGluing.Single.functor
        (algebraMap R (principalAdicCompletion f)) f).obj M.obj).snd) := sorry

/-- The object part of the finitely generated formal-gluing functor. -/
@[stacks 05ET "finite principal-adic formal-gluing object"]
noncomputable abbrev principalAdicFormalGlueingFGObj
    (M : FGModuleCat.{u} R) :
    CategoricalPullback
      (FGModuleCat.extendScalars
        (algebraMap (principalAdicCompletion f)
          (Localization.Away (algebraMap R (principalAdicCompletion f) f))))
      (FGModuleCat.extendScalars
        (Localization.awayMap (algebraMap R (principalAdicCompletion f)) f)) :=
  let X := (LocalizedModule.Away.FormalGluing.Single.functor
    (algebraMap R (principalAdicCompletion f)) f).obj M.obj
  CategoricalPullback.mk
    ⟨X.fst, principalAdicFormalGlueingSingleFunctor_fst_finite f M⟩
    ⟨X.snd, principalAdicFormalGlueingSingleFunctor_snd_finite f M⟩
    ((ModuleCat.isFG
      (Localization.Away (algebraMap R (principalAdicCompletion f) f))).isoMk X.iso)

/-- The compatibility square used by the morphism part of the finitely
generated formal-gluing functor. -/
@[stacks 05ET "finite principal-adic formal-gluing map square"]
theorem principalAdicFormalGlueingFGMap_comm
    {M N : FGModuleCat.{u} R} (g : M ⟶ N) :
    let φ := (LocalizedModule.Away.FormalGluing.Single.functor
      (algebraMap R (principalAdicCompletion f)) f).map g.hom
    (FGModuleCat.extendScalars
      (algebraMap (principalAdicCompletion f)
        (Localization.Away (algebraMap R (principalAdicCompletion f) f)))).map
          ((ModuleCat.isFG (principalAdicCompletion f)).homMk φ.fst) ≫
        (principalAdicFormalGlueingFGObj f N).iso.hom =
      (principalAdicFormalGlueingFGObj f M).iso.hom ≫
        (FGModuleCat.extendScalars
          (Localization.awayMap (algebraMap R (principalAdicCompletion f)) f)).map
            ((ModuleCat.isFG (Localization.Away f)).homMk φ.snd) := sorry

/-- The morphism part of the finitely generated formal-gluing functor. -/
@[stacks 05ET "finite principal-adic formal-gluing map"]
noncomputable abbrev principalAdicFormalGlueingFGMap
    {M N : FGModuleCat.{u} R} (g : M ⟶ N) :
    principalAdicFormalGlueingFGObj f M ⟶
      principalAdicFormalGlueingFGObj f N :=
  let φ := (LocalizedModule.Away.FormalGluing.Single.functor
    (algebraMap R (principalAdicCompletion f)) f).map g.hom
  CategoricalPullback.Hom.mk
    ((ModuleCat.isFG (principalAdicCompletion f)).homMk φ.fst)
    ((ModuleCat.isFG (Localization.Away f)).homMk φ.snd)
    (principalAdicFormalGlueingFGMap_comm f g)

/-- The morphism part preserves identities. -/
@[stacks 05ET "finite principal-adic formal-gluing map identity"]
theorem principalAdicFormalGlueingFGMap_id (M : FGModuleCat.{u} R) :
    principalAdicFormalGlueingFGMap f (𝟙 M) =
      𝟙 (principalAdicFormalGlueingFGObj f M) := sorry

/-- The morphism part preserves composition. -/
@[stacks 05ET "finite principal-adic formal-gluing map composition"]
theorem principalAdicFormalGlueingFGMap_comp
    {M N P : FGModuleCat.{u} R} (g : M ⟶ N) (h : N ⟶ P) :
    principalAdicFormalGlueingFGMap f (g ≫ h) =
      principalAdicFormalGlueingFGMap f g ≫
        principalAdicFormalGlueingFGMap f h := sorry

/-- The completion-localization gluing datum defines a functor from finite
`R`-modules to the pullback of the corresponding finite module categories. -/
@[stacks 05ET "finite principal-adic formal-gluing functor"]
noncomputable def principalAdicFormalGlueingFGFunctor :
    FGModuleCat.{u} R ⥤
      CategoricalPullback
        (FGModuleCat.extendScalars
          (algebraMap (principalAdicCompletion f)
            (Localization.Away (algebraMap R (principalAdicCompletion f) f))))
        (FGModuleCat.extendScalars
          (Localization.awayMap (algebraMap R (principalAdicCompletion f)) f)) where
  obj := principalAdicFormalGlueingFGObj f
  map := principalAdicFormalGlueingFGMap f
  map_id := principalAdicFormalGlueingFGMap_id f
  map_comp := principalAdicFormalGlueingFGMap_comp f

/-- For a Noetherian ring, the finite-module completion-localization formal-gluing
functor is an equivalence. -/
@[stacks 05ET "finite principal-adic formal-gluing equivalence"]
theorem principalAdicFormalGlueingFGFunctor_isEquivalence
    [IsNoetherianRing R] :
    Functor.IsEquivalence (principalAdicFormalGlueingFGFunctor f) := sorry
