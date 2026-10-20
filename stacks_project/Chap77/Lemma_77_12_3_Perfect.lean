module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_10_3_Composition
public import stacks_project.Chap77.Lemma_77_12_3_BaseChange

/-!
# Perfectness of derived global sections against a homotopy-limit coherator

Tensoring or taking internal Hom of the Situation 77.12.2 coherator against a perfect
object of `D(𝒪_X)` yields a perfect object of `D(A)`, and the finite-level scalar
extension comparisons are invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

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
    (Modules.pushforwardCompIso (S.stageMap n) (S.stageToSpace (n + 1))).hom.app
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
        (Modules.pushforwardCompIso (S.stageMap n) (S.stageToSpace (n + 1))).hom.app
          (S.moduleSheaf n) ≫
        eqToHom (congrArg (fun g : S.stageSpace n ⟶ S.space ↦
          (Modules.pushforward g).obj (S.moduleSheaf n)) (S.stageMap_comp_stageToSpace n)) :=
  sorry

/-- Tensoring the coherator of a homotopy limit of pushed stage sheaves with a perfect
object gives a perfect derived global-sections complex over the inverse-limit ring. -/
theorem globalSectionsTensor_isPerfect (S : ProperFlatFormalSystem)
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
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (hE : ModuleDerived.IsPerfect E) :
    DerivedCategory.IsPerfect (globalSectionsTensor S F Klim E) :=
  sorry

/-- The canonical scalar-extension comparison for tensor global sections from a formal
homotopy limit to each finite-level stage is an isomorphism. -/
theorem globalSectionsTensorBaseChangeMap_isIso (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardTransition S n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (hE : ModuleDerived.IsPerfect E) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    IsIso (globalSectionsTensorBaseChangeMap S F stageIso Klim P E n Ext) :=
  sorry

/-- Derived global internal Hom from a perfect object into the coherator of a homotopy
limit of pushed stage sheaves is perfect over the inverse-limit ring. -/
theorem globalHom_isPerfect (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardTransition S n)
    (Klim : ModuleDerived S.space)
    (hKlim : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (H : MonoidalClosed (ModuleDerived S.space))
    (E : ModuleDerived S.space) (hE : ModuleDerived.IsPerfect E) :
    DerivedCategory.IsPerfect (globalHom S F Klim H E) :=
  sorry

/-- The canonical scalar-extension comparison for derived global internal Hom from a
formal homotopy limit to each finite-level stage is an isomorphism. -/
theorem globalHomBaseChangeMap_isIso (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    [BraidedCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardTransition S n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (H : MonoidalClosed (ModuleDerived S.space)) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    [BraidedCategory (ModuleDerived (S.stageSpace n))]
    [(modulePullbackDerived (S.stageToSpace n)).Monoidal]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) (hE : ModuleDerived.IsPerfect E)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    IsIso (globalHomBaseChangeMap S F stageIso Klim P H n H_n E Ext) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
