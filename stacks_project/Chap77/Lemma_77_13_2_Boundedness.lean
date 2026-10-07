module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_19_1_Instances
public import stacks_project.Chap75.Remark_75_20_6_Counit
public import stacks_project.Chap77.Situation_77_13_1_FormalCompletion
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction

/-!
# Boundedness of the coherator of a formal-completion homotopy limit

The quasi-coherent coreflection of an ambient homotopy limit of the
pushforwards of a Situation 77.13.1 system is bounded above in `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

section

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]

/-- The successor map of the inverse system of derived pushforwards of the
stage complexes, obtained by adjoining the derived-pullback transition,
composing the iterated pushforward, and transporting along `S.comp_p`. -/
def pushforwardTransition (S : System A A_lim X Xn p q i) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))] :
    (Modules.pushforwardDerived (p (n + 1))).obj (S.K (n + 1)) ⟶
      (Modules.pushforwardDerived (p n)).obj (S.K n) :=
  (Modules.pushforwardDerived (p (n + 1))).map
      (((modulePullbackDerivedPushforwardAdjunction (i n)).homEquiv
          (S.K (n + 1)) (S.K n)) (S.transitionIso n).hom) ≫
    (Modules.pushforwardDerived.compIso (i n) (p (n + 1))).hom.app (S.K n) ≫
    eqToHom (congrArg (fun g : Xn n ⟶ X ↦
      (Modules.pushforwardDerived g).obj (S.K n)) (S.comp_p n))

/-- `pushforwardTransition` is the adjoint of the derived-pullback transition,
followed by the derived-pushforward composition isomorphism and the
identification `i n ≫ p (n + 1) = p n`. -/
theorem pushforwardTransition_spec (S : System A A_lim X Xn p q i) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))] :
    S.pushforwardTransition n =
      (Modules.pushforwardDerived (p (n + 1))).map
          (((modulePullbackDerivedPushforwardAdjunction (i n)).homEquiv
              (S.K (n + 1)) (S.K n)) (S.transitionIso n).hom) ≫
        (Modules.pushforwardDerived.compIso (i n) (p (n + 1))).hom.app (S.K n) ≫
        eqToHom (congrArg (fun g : Xn n ⟶ X ↦
          (Modules.pushforwardDerived g).obj (S.K n)) (S.comp_p n)) :=
  sorry

/-- The quasi-coherent coreflection of an ambient homotopy limit of the
pushforwards of a formal-completion system is bounded above. -/
theorem coheratorHomotopyLimit_isBoundedAbove (S : System A A_lim X Xn p q i)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (hKlim : HomotopyLimit.IsOf Ksys Klim) :
    DerivedCategory.IsBoundedAbove
      ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]

/-- The quasicoherent coreflection of a sequential homotopy limit in `D(𝒪_X)` is a
homotopy limit of the coreflected stages in `DerivedQCoh X`. -/
theorem rightAdjoint_preservesHomotopyLimit
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (Klim : ModuleDerived X) (hKlim : HomotopyLimit.IsOf Ksys Klim) :
    HomotopyLimit.IsOf (Ksys ⋙ (inclusion X).rightAdjoint)
      ((inclusion X).rightAdjoint.obj Klim) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
