/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap77.Lemma_77_12_5_Comparison
public import stacks_project.Chap77.Lemma_77_12_6_SpecialFiber

/-!
# Concentration of the coherator homotopy limit near the special fiber

On an open neighborhood of the special fiber, the quasi-coherent coreflection of a
homotopy limit of pushed stage sheaves is concentrated in degree zero, its
degree-zero cohomology is of finite presentation, and it pulls back to each
stage sheaf `ℱ n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The restriction `H^j(K)|_W` of a cohomology sheaf of the coherator homotopy
limit to an open subspace of the limit space. -/
def restrictCohomology (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (W : OpenSubspace S.space) (j : ℤ) : W.X.Modules :=
  (Modules.pullback W.ι).obj
    ((DerivedCategory.homologyFunctor (Modules S.space) j).obj
      (homotopyLimitCoherator S F Klim))

/-- `restrictCohomology` is underived pullback of degree-`j` homology of
`homotopyLimitCoherator`. -/
theorem restrictCohomology_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (W : OpenSubspace S.space) (j : ℤ) :
    restrictCohomology S F Klim W j =
      (Modules.pullback W.ι).obj
        ((DerivedCategory.homologyFunctor (Modules S.space) j).obj
          (homotopyLimitCoherator S F Klim)) :=
  sorry

/-- The sheaf `ℱ = H^0(K)|_W` on an open subspace of the limit space. -/
def restrictDegreeZero (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (W : OpenSubspace S.space) : W.X.Modules :=
  restrictCohomology S F Klim W 0

/-- `restrictDegreeZero` is `restrictCohomology` in degree zero. -/
theorem restrictDegreeZero_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (W : OpenSubspace S.space) :
    restrictDegreeZero S F Klim W = restrictCohomology S F Klim W 0 :=
  sorry

/-- The canonical map `H^0(K) ⟶ i_{n*} ℱ n` on the limit space, obtained by
taking degree-zero homology of the comparison from the coherator through the
presented homotopy-limit stage and the identification of that stage with the
degree-zero single of `pushforwardModule n`. -/
def cohomologyToStagePushforward (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ) :
    (DerivedCategory.homologyFunctor (Modules S.space) 0).obj
      (homotopyLimitCoherator S F Klim) ⟶
    S.pushforwardModule n :=
  (DerivedCategory.homologyFunctor (Modules S.space) 0).map
      (coheratorCounit S F Klim ≫ P.stageProjection n ≫
        (DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)).map
          (stageIso n).hom) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules S.space) 0).hom.app
      (S.pushforwardModule n)

/-- `cohomologyToStagePushforward` is degree-zero homology of the coherator-to-stage
comparison, followed by the single-complex identification of `pushforwardModule n`. -/
theorem cohomologyToStagePushforward_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ) :
    cohomologyToStagePushforward S F stageIso Klim P n =
      (DerivedCategory.homologyFunctor (Modules S.space) 0).map
          (coheratorCounit S F Klim ≫ P.stageProjection n ≫
            (DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)).map
              (stageIso n).hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules S.space) 0).hom.app
          (S.pushforwardModule n) :=
  sorry

/-- The canonical comparison `i_n^* H^0(K) ⟶ ℱ n`, the adjunct of
`cohomologyToStagePushforward`. This is the meaning of
`ℱ n = H^0(K) ⊗_{𝒪_X} 𝒪_{X_n}`. -/
def cohomologyToStage (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ) :
    (Modules.pullback (S.stageToSpace n)).obj
      ((DerivedCategory.homologyFunctor (Modules S.space) 0).obj
        (homotopyLimitCoherator S F Klim)) ⟶
    S.moduleSheaf n :=
  ((Modules.pullbackPushforwardAdjunction (S.stageToSpace n)).homEquiv
      ((DerivedCategory.homologyFunctor (Modules S.space) 0).obj
        (homotopyLimitCoherator S F Klim))
      (S.moduleSheaf n)).symm
    (cohomologyToStagePushforward S F stageIso Klim P n)

/-- `cohomologyToStage` is the underived pullback-pushforward adjunct of
`cohomologyToStagePushforward`. -/
theorem cohomologyToStage_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ) :
    cohomologyToStage S F stageIso Klim P n =
      ((Modules.pullbackPushforwardAdjunction (S.stageToSpace n)).homEquiv
          ((DerivedCategory.homologyFunctor (Modules S.space) 0).obj
            (homotopyLimitCoherator S F Klim))
          (S.moduleSheaf n)).symm
        (cohomologyToStagePushforward S F stageIso Klim P n) :=
  sorry

/-- An open subspace of the limit space on which the coherator homotopy limit is
concentrated in degree zero, with finitely presented degree-zero cohomology, and
with canonical identification of each stage sheaf. -/
structure IsConcentratedFinitePresentationOpen (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (W : OpenSubspace S.space) : Prop where
  /-- The special fiber is contained in the open subspace. -/
  containsSpecialFiber : specialFiberPoints S ⊆ W.pointsSet
  /-- Restricted cohomology of the coherator vanishes off degree zero. -/
  vanishing : ∀ j : ℤ, j ≠ 0 → IsZero (restrictCohomology S F Klim W j)
  /-- The sheaf `H^0(K)|_W` is of finite presentation. -/
  finitePresentation : (restrictDegreeZero S F Klim W).IsFinitePresentation
  /-- Each stage sheaf is identified with the pullback of `H^0(K)` along `X_n ⟶ X`. -/
  isIso_cohomologyToStage : ∀ n, IsIso (cohomologyToStage S F stageIso Klim P n)

/-- Package the four source conditions on an open subspace of the limit space. -/
def IsConcentratedFinitePresentationOpen.of (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (W : OpenSubspace S.space)
    (containsSpecialFiber : specialFiberPoints S ⊆ W.pointsSet)
    (vanishing : ∀ j : ℤ, j ≠ 0 → IsZero (restrictCohomology S F Klim W j))
    (finitePresentation : (restrictDegreeZero S F Klim W).IsFinitePresentation)
    (isIso_cohomologyToStage : ∀ n, IsIso (cohomologyToStage S F stageIso Klim P n)) :
    IsConcentratedFinitePresentationOpen S F stageIso Klim P W where
  containsSpecialFiber := containsSpecialFiber
  vanishing := vanishing
  finitePresentation := finitePresentation
  isIso_cohomologyToStage := isIso_cohomologyToStage

/-- The concentration-and-finite-presentation predicate is equivalent to containment of
the special fiber, vanishing of restricted cohomology off degree zero, finite
presentation of `H^0(K)|_W`, and invertibility of `cohomologyToStage`. -/
theorem IsConcentratedFinitePresentationOpen_iff (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (W : OpenSubspace S.space) :
    IsConcentratedFinitePresentationOpen S F stageIso Klim P W ↔
      specialFiberPoints S ⊆ W.pointsSet ∧
        (∀ j : ℤ, j ≠ 0 → IsZero (restrictCohomology S F Klim W j)) ∧
          (restrictDegreeZero S F Klim W).IsFinitePresentation ∧
            ∀ n, IsIso (cohomologyToStage S F stageIso Klim P n) :=
  sorry

/-- On an open subspace satisfying `IsConcentratedFinitePresentationOpen`, the sheaf
`H^0(K)|_W` is of finite presentation. -/
theorem restrictDegreeZero_isFinitePresentation (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (W : OpenSubspace S.space)
    (hW : IsConcentratedFinitePresentationOpen S F stageIso Klim P W) :
    (restrictDegreeZero S F Klim W).IsFinitePresentation :=
  sorry

/-- In Situation 77.12.1, with `K` the quasi-coherent coreflection of a homotopy
limit of the pushed stage sheaves, some open subspace of `X` contains the special
fiber, concentrates `K` in degree zero, makes `H^0(K)` finitely presented, and
identifies each stage sheaf with the pullback of that degree-zero cohomology. -/
theorem existsOpen_coheratorLimit_concentrated_finitePresentation
    (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushedStageSuccessor S n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim) :
    ∃ W : OpenSubspace S.space,
      IsConcentratedFinitePresentationOpen S F stageIso Klim P W :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
