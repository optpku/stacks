module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineBaseChange

/-!
# Base change for pushed-forward Čech complexes

Pushed-forward Čech complexes associated to finite affine open covers commute with scheme base
change and represent the bounded-below derived pushforward after base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OpenCoverCech

variable {X S S' : Scheme.{u}} {ι : Type u}

/-- Stacks Project, Lemma 30.7.2 (tag 01XM): termwise base change for a pushed-forward Čech
complex. -/
@[stacks 01XM]
theorem baseChange_isomorphic
    (f : X ⟶ S) (g : S' ⟶ S)
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    [Finite ι]
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (OpenCoverCech.pushforward f 𝒰 ℱ))
      (OpenCoverCech.pushforward (pullback.snd f g)
        (baseChangeOpenFamily f g 𝒰)
        (Scheme.Modules.baseChangeModule f g ℱ)) := sorry

/-- Stacks Project, Lemma 30.7.2 (tag 01XM): derived base change for a pushed-forward Čech
complex. -/
@[stacks 01XM]
theorem derivedBaseChange_isomorphic
    (f : X ⟶ S) (g : S' ⟶ S)
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    [Finite ι]
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient S'.Modules).obj
          (((Scheme.Modules.pullback g).mapCochainComplexPlus).obj
            ((CochainComplex.Plus.extendNat S.Modules).obj
              (OpenCoverCech.pushforward f 𝒰 ℱ)))))
      ((Scheme.Modules.pushforward (pullback.snd f g)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (pullback f g : Scheme.{u}).Modules 0).obj
          (Scheme.Modules.baseChangeModule f g ℱ))) := sorry

end AlgebraicGeometry.Scheme.OpenCoverCech
