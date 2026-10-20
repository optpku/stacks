module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Retract
public import ReasLib.Algebra.Category.ModuleCat.Pure
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Criteria

@[expose] public section

open CategoryTheory
open scoped DirectSum

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Every module over a commutative ring is the last term of a universally exact short
complex whose middle term is pure projective. -/
theorem exists_universallyExact_pureProjective_presentation (M : ModuleCat.{u} R) :
    ∃ (N P : ModuleCat.{u} R) (f : N ⟶ P) (g : P ⟶ M) (hzero : f ≫ g = 0),
      (ShortComplex.mk f g hzero).UniversallyExact ∧ P.PureProjective := sorry

namespace PureProjective

/-- A module over a commutative ring is pure projective exactly when it is a retract of a
direct sum of finitely presented modules. -/
theorem iff_retract_directSum_finitePresentation (M : ModuleCat.{u} R) :
    M.PureProjective ↔
      ∃ (ι : Type u) (P : ι → ModuleCat.{u} R),
        (∀ i, Module.FinitePresentation R (P i)) ∧
          Nonempty (CategoryTheory.Retract M (ModuleCat.of R (⨁ i, P i))) := sorry

end PureProjective

end ModuleCat
