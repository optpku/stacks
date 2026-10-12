/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.ContentIdeal
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.LinearAlgebra.UniversallyInjective

@[expose] public section

universe u v w x y z

namespace Module.PureSpreadout

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (S : Submonoid B) {N : Type w} [AddCommGroup N]
variable [Module (Localization S) N] [Module B N] [Module A N]
variable [IsScalarTower B (Localization S) N] [IsScalarTower A B N]
variable [Module.FinitePresentation (Localization S) N]
variable {N' : Type x} [AddCommGroup N'] [Module B N'] [Module A N']
variable [IsScalarTower A B N'] [Module.FinitePresentation B N']
variable [Module.Projective A N']

/-- Every element of a finitely presented localization module with a projective,
universally injective spreadout has a content ideal over the base ring. -/
theorem existsContentIdeal
    (hAB : (algebraMap A B).FinitePresentation) (ι : N' →ₗ[B] N)
    [IsLocalizedModule S ι]
    (hι : LinearMap.UniversallyInjective.{u, x, w, max u v w x}
      (ι.restrictScalars A))
    (n : N) : ∃ I : Ideal A, IsContentIdeal n I := sorry

/-- A linear map from a finitely presented localization module with a projective,
universally injective spreadout to a flat module is universally injective if it
is injective modulo every maximal ideal of the base ring. -/
theorem universallyInjective_of_injective_mod_maximalIdeal
    (hAB : (algebraMap A B).FinitePresentation) (ι : N' →ₗ[B] N)
    [IsLocalizedModule S ι]
    (hι : LinearMap.UniversallyInjective.{u, x, w, max u v w x y z}
      (ι.restrictScalars A))
    {M : Type y} [AddCommGroup M] [Module A M] [Module.Flat A M]
    (f : N →ₗ[A] M)
    (hf : ∀ (m : Ideal A) [m.IsMaximal],
      Function.Injective (f.quotientMapByIdeal m)) :
    LinearMap.UniversallyInjective.{u, w, y, max u v w x y z} f := sorry

end Module.PureSpreadout
