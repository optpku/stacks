module

public import stacks_project.Chap77.Lemma_77_13_3_Comparison

/-!
# Lemma 77.13.3

In Situation 77.13.1, with `K` as in Lemma 77.13.2, tensoring with a perfect
object of `D(𝒪_X)` yields pseudo-coherent derived global sections over `A`,
together with a canonical isomorphism after derived base change to each `A_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open FormalCompletion FormalCompletion.System
open CategoryTheory.DerivedCategory

noncomputable section

universe u

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]

/-- Lemma 77.13.3 (1): in Situation 77.13.1, with `K` as in Lemma 77.13.2, for every
perfect object `E` of `D(𝒪_X)` the object `M = RΓ(X, K ⊗ᴸ E)` is pseudo-coherent in
`D(A)`. -/
@[stacks 0DIM]
theorem globalSectionsTensor_isPseudoCoherent
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (hKlim : HomotopyLimit.IsOf Ksys Klim)
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) :
    DerivedCategory.IsPseudoCoherent
      (globalSectionsTensor Klim E) :=
  sorry

/-- Lemma 77.13.3 (2): in Situation 77.13.1, with `K` as in Lemma 77.13.2, for every
perfect object `E` of `D(𝒪_X)` there is a canonical isomorphism
`RΓ(X_n, K_n ⊗ᴸ E|_{X_n}) = M ⊗ᴸ_A A_n` in `D(A_n)`, realized as invertibility of
`globalSectionsTensorBaseChangeMap`. Here `E|_{X_n}` denotes the derived pullback
`L(p n)^* E`. -/
@[stacks 0DIM]
theorem globalSectionsTensorBaseChangeMap_isIso
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    IsIso (globalSectionsTensorBaseChangeMap S Ksys stageIso Klim P E n Ext) :=
  sorry

