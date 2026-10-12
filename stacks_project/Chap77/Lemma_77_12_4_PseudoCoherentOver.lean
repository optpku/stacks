/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap76.Lemma_76_45_4_Relative
public import stacks_project.Chap77.Lemma_77_12_2_HomotopyLimit
public import stacks_project.Chap77.Lemma_77_12_3_Instances

/-!
# Relative pseudo-coherence of the coherator of a formal homotopy limit

The quasi-coherent coreflection of an ambient homotopy limit of the pushed stage
sheaves of a proper flat formal system is pseudo-coherent relative to the
inverse-limit ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The successor map of pushed stage sheaves, obtained by adjoining the stage
transition isomorphism, composing the iterated pushforward, and transporting along
`stageMap_comp_stageToSpace`. -/
def pushforwardTransition (S : ProperFlatFormalSystem) (n : ℕ) :
    S.pushforwardModule (n + 1) ⟶ S.pushforwardModule n :=
  (Modules.pushforward (S.stageToSpace (n + 1))).map
      (((Modules.pullbackPushforwardAdjunction (S.stageMap n)).homEquiv
          (S.moduleSheaf (n + 1)) (S.moduleSheaf n)) (S.moduleTransitionIso n).hom) ≫
    (Modules.pushforwardComp (S.stageMap n) (S.stageToSpace (n + 1))).hom.app
      (S.moduleSheaf n) ≫
    eqToHom (congrArg (fun g : S.stageSpace n ⟶ S.space ↦
      (Modules.pushforward g).obj (S.moduleSheaf n)) (S.stageMap_comp_stageToSpace n))

/-- `pushforwardTransition` is the adjoint of the stage transition, followed by the
pushforward composition isomorphism and the identification
`stageMap n ≫ stageToSpace (n + 1) = stageToSpace n`. -/
theorem pushforwardTransition_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    pushforwardTransition S n =
      (Modules.pushforward (S.stageToSpace (n + 1))).map
          (((Modules.pullbackPushforwardAdjunction (S.stageMap n)).homEquiv
              (S.moduleSheaf (n + 1)) (S.moduleSheaf n)) (S.moduleTransitionIso n).hom) ≫
        (Modules.pushforwardComp (S.stageMap n) (S.stageToSpace (n + 1))).hom.app
          (S.moduleSheaf n) ≫
        eqToHom (congrArg (fun g : S.stageSpace n ⟶ S.space ↦
          (Modules.pushforward g).obj (S.moduleSheaf n)) (S.stageMap_comp_stageToSpace n)) :=
  sorry

/-- The quasi-coherent coreflection of an ambient homotopy limit of the pushed stage
sheaves is pseudo-coherent relative to the inverse-limit ring. -/
theorem coheratorHomotopyLimit_isPseudoCoherentOver (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardTransition S n)
    (Klim : ModuleDerived S.space)
    (hKlim : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor S.space.Modules (0 : ℤ)) Klim) :
    ModuleDerived.IsPseudoCoherentOver (toBase S.space)
      ((DerivedQCoh.inclusion S.space).rightAdjoint.obj Klim).obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
