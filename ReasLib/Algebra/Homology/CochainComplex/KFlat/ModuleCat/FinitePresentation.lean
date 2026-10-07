module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Detecting K-flatness on finitely presented modules

@stack 0E8F

For complexes of modules, K-flatness can be detected by tensoring with finitely presented
modules placed in degree zero.  This is the commutative-ring specialization supported by the
symmetric monoidal structure on `ModuleCat`.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Lemma 15.59.9 (0E8F), in the commutative-ring setting: if tensoring `K` with every finitely
presented module in degree zero is acyclic, then `K` is K-flat. -/
@[stacks 0E8F "detecting K-flatness on finitely presented modules"]
theorem isKFlat_of_tensor_finitelyPresented_acyclic
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K
        ((singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).Acyclic) :
    K.IsKFlat := sorry

end CochainComplex
