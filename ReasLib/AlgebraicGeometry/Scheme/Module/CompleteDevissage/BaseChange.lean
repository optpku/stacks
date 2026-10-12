/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.BaseChange

/-!
# Base change of complete dévissages

This file constructs the stagewise pullback of a complete dévissage along an affine pointed
base change.  The comparison morphisms are the canonical mates for the cartesian squares.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.CompleteDevissageOver

namespace Stage

variable {S S' : Scheme.{u}} {s : S}

/-- The square obtained by pulling a stage morphism back along a base morphism commutes. -/
theorem baseChangeCommSq (T : Stage S s) (g : S' ⟶ S) :
    CommSq (pullback.fst T.Z.hom g) ((Over.pullback g).map T.π).left
      T.π.left (pullback.fst T.Y.hom g) :=
  ⟨(pullback.lift_fst _ _ _).symm⟩

/-- The canonical comparison from the pullback of the stage pushforward to the pushforward of
the pulled-back stage module. -/
noncomputable def pushforwardBaseChangeMap (T : Stage S s) (g : S' ⟶ S) :
    (Scheme.Modules.pullback (pullback.fst T.Y.hom g)).obj
        ((Scheme.Modules.pushforward T.π.left).obj T.G) ⟶
      (Scheme.Modules.pushforward ((Over.pullback g).map T.π).left).obj
        (Scheme.Modules.baseChangeModule T.Z.hom g T.G) :=
  (RingedSpace.Hom.BaseChange.map
    ((T.baseChangeCommSq g).map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))).app T.G

/-- `pushforwardBaseChangeMap` is the canonical underived base-change comparison for the
cartesian square of a stage. -/
theorem pushforwardBaseChangeMap_def (T : Stage S s) (g : S' ⟶ S) :
    T.pushforwardBaseChangeMap g =
      (RingedSpace.Hom.BaseChange.map
        ((T.baseChangeCommSq g).map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace))).app T.G := sorry

/-- The comparison map of the pulled-back stage, formed from pullback of the original map and
the canonical free-sheaf and pushforward base-change comparisons. -/
noncomputable def baseChangeAlpha (T : Stage S s) (g : S' ⟶ S) :
    (SheafOfModules.freeFin T.rank : ((Over.pullback g).obj T.Y).left.Modules) ⟶
      (Scheme.Modules.pushforward ((Over.pullback g).map T.π).left).obj
        (Scheme.Modules.baseChangeModule T.Z.hom g T.G) :=
  (SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom (pullback.fst T.Y.hom g).toShHom)
      (ULift.{u} (Fin T.rank))).inv ≫
    (Scheme.Modules.pullback (pullback.fst T.Y.hom g)).map T.α ≫
      T.pushforwardBaseChangeMap g

/-- `baseChangeAlpha` is the canonical composite giving the pulled-back stage comparison. -/
theorem baseChangeAlpha_def (T : Stage S s) (g : S' ⟶ S) :
    T.baseChangeAlpha g =
      (SheafOfModules.pullbackObjFreeIso
          (RingedSpace.Hom.toRingCatSheafHom (pullback.fst T.Y.hom g).toShHom)
          (ULift.{u} (Fin T.rank))).inv ≫
        (Scheme.Modules.pullback (pullback.fst T.Y.hom g)).map T.α ≫
          T.pushforwardBaseChangeMap g := sorry

/-- Affine pushforward base change makes the canonical stage comparison invertible. -/
theorem pushforwardBaseChangeMap_isIso (T : Stage S s) (g : S' ⟶ S)
    [IsFinite T.π.left] [T.G.IsQuasicoherent] : IsIso (T.pushforwardBaseChangeMap g) := sorry

end Stage

variable {S S' X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}

variable [h_f : LocallyOfFiniteType f] [h_Fqc : F.IsQuasicoherent]
  [h_Fft : F.IsFiniteType]


/-- Pullback carries the cokernel of a stage comparison to the cokernel of its canonical
base-changed comparison, up to isomorphism. -/
theorem baseChangeCokernel_isomorphic (T : Stage S s) (g : S' ⟶ S)
    [IsFinite T.π.left] [T.G.IsQuasicoherent] :
    IsIsomorphic
      ((Scheme.Modules.pullback (pullback.fst T.Y.hom g)).obj (cokernel T.α))
      (cokernel (T.baseChangeAlpha g)) := sorry

/-- The pulled-back comparison is bijective on the selected generic-point fibre. -/
theorem baseChangeStage_fiberBijective (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] :
    Function.Bijective (Scheme.Modules.fiberMap ((D.stage k).baseChangeAlpha g)
      (((Over.pullback g).obj (D.stage k).Y).hom.fiberι s' (ξ' k))) := sorry

/-- Pull back one stage of a complete dévissage, retaining its rank and using the supplied
generic point of the new fibre. -/
noncomputable def baseChangeStage (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] : Stage S' s' :=
  Stage.ofComponents ((Over.pullback g).obj (D.stage k).Z)
    ((Over.pullback g).obj (D.stage k).Y) ((Over.pullback g).map (D.stage k).π)
    (Scheme.Modules.baseChangeModule (D.stage k).Z.hom g (D.stage k).G)
    (D.stage k).rank ((D.stage k).baseChangeAlpha g) (ξ' k) (hξ' k)
    (fun _ hη ↦ hη.eq (hξ' k))
    (baseChangeStage_fiberBijective D g s' h_point ξ' hξ' k)

/-- The auxiliary scheme of a pulled-back stage is the canonical base change. -/
theorem baseChangeStage_Z (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] :
    (D.baseChangeStage g s' h_point ξ' hξ' k).Z =
      (Over.pullback g).obj (D.stage k).Z := sorry

/-- The model of a pulled-back stage is the canonical base change. -/
theorem baseChangeStage_Y (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] :
    (D.baseChangeStage g s' h_point ξ' hξ' k).Y =
      (Over.pullback g).obj (D.stage k).Y := sorry

/-- The finite map of a pulled-back stage is the canonical pulled-back map. -/
theorem baseChangeStage_π (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] :
    (D.baseChangeStage g s' h_point ξ' hξ' k).π =
      (Over.pullback g).map (D.stage k).π := sorry

/-- The module of a pulled-back stage is the canonical module base change. -/
theorem baseChangeStage_G (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] :
    (D.baseChangeStage g s' h_point ξ' hξ' k).G =
      Scheme.Modules.baseChangeModule (D.stage k).Z.hom g (D.stage k).G := sorry

/-- Base change leaves the rank of a stage unchanged. -/
theorem baseChangeStage_rank (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] :
    (D.baseChangeStage g s' h_point ξ' hξ' k).rank = (D.stage k).rank := sorry

/-- The comparison map of a pulled-back stage is `baseChangeAlpha`. -/
theorem baseChangeStage_α (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] :
    (D.baseChangeStage g s' h_point ξ' hξ' k).α =
      (D.stage k).baseChangeAlpha g := sorry

/-- The selected point of a pulled-back stage is the supplied generic point. -/
theorem baseChangeStage_ξ (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [IsAffine S'] :
    (D.baseChangeStage g s' h_point ξ' hξ' k).ξ = ξ' k := sorry

/-- The pulled-back first stage is a one-step dévissage of the pulled-back source module. -/
theorem baseChangeInitialStep (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    [IsAffine S'] :
    IsOneStepDevissageOver ((Over.pullback g).obj (Over.mk f))
      (Scheme.Modules.baseChangeModule f g F) s'
      (D.baseChangeStage g s' h_point ξ' hξ' 0).Z
      (D.baseChangeStage g s' h_point ξ' hξ' 0).Y
      ((Over.pullback g).map D.initial)
      (D.baseChangeStage g s' h_point ξ' hξ' 0).π
      (D.baseChangeStage g s' h_point ξ' hξ' 0).G := sorry

/-- Every pulled-back successor stage is a one-step dévissage of the preceding pulled-back
comparison cokernel. -/
theorem baseChangeTransitionStep (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (i : Fin D.last) [IsAffine S'] :
    IsOneStepDevissageOver
      (D.baseChangeStage g s' h_point ξ' hξ' i.castSucc).Y
      (cokernel (D.baseChangeStage g s' h_point ξ' hξ' i.castSucc).α) s'
      (D.baseChangeStage g s' h_point ξ' hξ' i.succ).Z
      (D.baseChangeStage g s' h_point ξ' hξ' i.succ).Y
      ((Over.pullback g).map (D.transition i))
      (D.baseChangeStage g s' h_point ξ' hξ' i.succ).π
      (D.baseChangeStage g s' h_point ξ' hξ' i.succ).G := sorry

/-- The cokernel of the last pulled-back comparison map is zero. -/
theorem baseChangeTerminal (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    [IsAffine S'] :
    IsZero (cokernel
      (D.baseChangeStage g s' h_point ξ' hξ' (Fin.last D.last)).α) := sorry

/-- Pull a complete dévissage back along an affine pointed morphism. -/
noncomputable def baseChange (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    [IsAffine S'] :
    @CompleteDevissageOver S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s' :=
  @CompleteDevissageOver.ofStages S' ((Over.pullback g).obj (Over.mk f)).left
    ((Over.pullback g).obj (Over.mk f)).hom
    (Scheme.Modules.baseChangeModule f g F :
      ((Over.pullback g).obj (Over.mk f)).left.Modules)
    (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
    (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
    (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s' D.last
    (fun k ↦ D.baseChangeStage g s' h_point ξ' hξ' k) ((Over.pullback g).map D.initial)
    (baseChangeInitialStep D g s' h_point ξ' hξ')
    (fun i ↦ (Over.pullback g).map (D.transition i))
    (fun i ↦ baseChangeTransitionStep D g s' h_point ξ' hξ' i)
    (baseChangeTerminal D g s' h_point ξ' hξ')

/-- Base change preserves the number of stages in a complete dévissage. -/
theorem baseChange_last (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    [hS' : IsAffine S'] :
    @CompleteDevissageOver.last S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s'
      (@baseChange S S' X f F s h_f h_Fqc h_Fft D g s' h_point ξ' hξ' hS') =
        D.last := sorry

/-- The stages of the base-changed complete dévissage are the explicitly pulled-back stages. -/
theorem baseChange_stage (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (k : Fin (D.last + 1)) [hS' : IsAffine S'] :
    @CompleteDevissageOver.stage S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s'
      (@baseChange S S' X f F s h_f h_Fqc h_Fft D g s' h_point ξ' hξ' hS') k =
        D.baseChangeStage g s' h_point ξ' hξ' k := sorry

/-- The initial immersion of the base-changed dévissage is the canonical pullback. -/
theorem baseChange_initial (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    [hS' : IsAffine S'] :
    @CompleteDevissageOver.initial S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s'
      (@baseChange S S' X f F s h_f h_Fqc h_Fft D g s' h_point ξ' hξ' hS') =
        (Over.pullback g).map D.initial := sorry

/-- Every transition of the base-changed dévissage is the canonical pullback transition. -/
theorem baseChange_transition (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s')
    (hξ' : ∀ k, IsGenericPoint (ξ' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')))
    (i : Fin D.last) [hS' : IsAffine S'] :
    @CompleteDevissageOver.transition S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s'
      (@baseChange S S' X f F s h_f h_Fqc h_Fft D g s' h_point ξ' hξ' hS') i =
        (Over.pullback g).map (D.transition i) := sorry

/-- The canonical generic point of the fibre of the base change of the model at a stage. -/
noncomputable def baseChangeStageGenericPoint (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (k : Fin (D.last + 1)) :
    ((Over.pullback g).obj (D.stage k).Y).hom.fiber s' :=
  -- Local instance justification (proof-local temporary data): the irreducibility proof is derived from the explicit stage solely to form its canonical generic point; a global instance would depend on explicit structure data.
  letI : GeometricallyIrreducible (D.stage k).Y.hom :=
    Fin.cases D.initialStep.geometricallyIrreducible
      (fun i ↦ (D.transitionStep i).geometricallyIrreducible) k
  -- Local instance justification (defeq pin): expose the canonical base-change instance through the `Over.pullback` projection used by the fibre.
  letI : GeometricallyIrreducible ((Over.pullback g).obj (D.stage k).Y).hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd (D.stage k).Y.hom g))
  genericPoint (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')

/-- The canonical point chosen on a base-changed stage fibre is a generic point. -/
theorem baseChangeStageGenericPoint_isGeneric (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (k : Fin (D.last + 1)) :
    IsGenericPoint (D.baseChangeStageGenericPoint g s' k)
      (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s')) := sorry

/-- Pull a complete dévissage back along an affine pointed morphism, choosing the generic point
of each base-changed model fibre canonically. -/
noncomputable def baseChangeCanonical (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @CompleteDevissageOver S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s' :=
  D.baseChange g s' h_point (D.baseChangeStageGenericPoint g s')
    (D.baseChangeStageGenericPoint_isGeneric g s')

/-- Canonical base change preserves the number of stages in a complete dévissage. -/
theorem baseChangeCanonical_last (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @CompleteDevissageOver.last S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s'
      (@baseChangeCanonical S S' X f F s h_f h_Fqc h_Fft D g s' h_point hS') =
        D.last := sorry

/-- The stages of the canonical base change are the pulled-back stages with their canonical
generic points. -/
theorem baseChangeCanonical_stage (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (k : Fin (D.last + 1)) [hS' : IsAffine S'] :
    @CompleteDevissageOver.stage S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s'
      (@baseChangeCanonical S S' X f F s h_f h_Fqc h_Fft D g s' h_point hS') k =
      D.baseChangeStage g s' h_point (D.baseChangeStageGenericPoint g s')
        (D.baseChangeStageGenericPoint_isGeneric g s') k := sorry

/-- The initial immersion of the canonical base change is the pulled-back initial immersion. -/
theorem baseChangeCanonical_initial (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @CompleteDevissageOver.initial S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s'
      (@baseChangeCanonical S S' X f F s h_f h_Fqc h_Fft D g s' h_point hS') =
        (Over.pullback g).map D.initial := sorry

/-- Every transition of the canonical base change is the corresponding pulled-back
transition. -/
theorem baseChangeCanonical_transition (D : CompleteDevissageOver f F s)
    (g : S' ⟶ S) (s' : S') (h_point : g s' = s)
    (i : Fin D.last) [hS' : IsAffine S'] :
    @CompleteDevissageOver.transition S' ((Over.pullback g).obj (Over.mk f)).left
      ((Over.pullback g).obj (Over.mk f)).hom
      (Scheme.Modules.baseChangeModule f g F :
        ((Over.pullback g).obj (Over.mk f)).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) s'
      (@baseChangeCanonical S S' X f F s h_f h_Fqc h_Fft D g s' h_point hS') i =
        (Over.pullback g).map (D.transition i) := sorry

end AlgebraicGeometry.Scheme.Modules.CompleteDevissageOver
