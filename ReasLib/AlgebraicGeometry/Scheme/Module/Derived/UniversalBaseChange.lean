/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

/-!
# Universal complexes for derived pushforward after base change

A universal derived-pushforward complex is a bounded-below complex of quasicoherent modules
whose pullback represents derived pushforward after every scheme base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- A bounded-below complex of quasicoherent modules whose pullback along every morphism of
schemes represents the derived pushforward of the corresponding base-changed module. -/
@[stacks 01XN "universal complex for derived pushforward after base change"]
def IsUniversalDerivedPushforwardComplex
    (f : X ⟶ S) (ℱ : X.Modules) (K : CochainComplex.Plus S.Modules) : Prop :=
  (∀ p : ℤ, (K.obj.X p).IsQuasicoherent) ∧
    ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S)
      [EnoughInjectives (pullback f g : Scheme.{u}).Modules],
      IsIsomorphic
        (DerivedCategory.Plus.Qh.obj
          ((HomotopyCategory.Plus.quotient S'.Modules).obj
            (((Scheme.Modules.pullback g).mapCochainComplexPlus).obj K)))
        ((Scheme.Modules.pushforward (pullback.snd f g)).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (pullback f g : Scheme.{u}).Modules 0).obj
            (Scheme.Modules.baseChangeModule f g ℱ)))

/-- Every term of a universal derived-pushforward complex is quasicoherent. -/
theorem IsUniversalDerivedPushforwardComplex.term_isQuasicoherent
    {f : X ⟶ S} {ℱ : X.Modules} {K : CochainComplex.Plus S.Modules}
    (hK : IsUniversalDerivedPushforwardComplex f ℱ K) (p : ℤ) :
    (K.obj.X p).IsQuasicoherent :=
  hK.1 p

/-- Pulling back a universal derived-pushforward complex represents the derived pushforward of
the base-changed module. -/
theorem IsUniversalDerivedPushforwardComplex.pullback_isomorphic
    {f : X ⟶ S} {ℱ : X.Modules} {K : CochainComplex.Plus S.Modules}
    (hK : IsUniversalDerivedPushforwardComplex f ℱ K)
    {S' : Scheme.{u}} (g : S' ⟶ S)
    [EnoughInjectives (pullback f g : Scheme.{u}).Modules] :
    IsIsomorphic
      (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient S'.Modules).obj
          (((Scheme.Modules.pullback g).mapCochainComplexPlus).obj K)))
      ((Scheme.Modules.pushforward (pullback.snd f g)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (pullback f g : Scheme.{u}).Modules 0).obj
          (Scheme.Modules.baseChangeModule f g ℱ))) :=
  hK.2 g

/-- For a quasi-compact quasi-separated morphism to a quasi-compact separated scheme, every
quasicoherent module admits a universal bounded-below derived-pushforward complex. -/
@[stacks 01XN "existence of a universal derived-pushforward complex"]
theorem exists_universalDerivedPushforwardComplex
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S.carrier] [S.IsSeparated]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∃ K : CochainComplex.Plus S.Modules,
      IsUniversalDerivedPushforwardComplex f ℱ K := sorry

end AlgebraicGeometry.Scheme
