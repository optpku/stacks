/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso.Bounded
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Existence
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective.Bounded
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

@[expose] public section

/-!
# Global Bounded Right Derived Functors from Injective Resolutions

This leaf globalizes bounded-below K-injective computation without choosing a
derived-category model.  Its general entry point only assumes an objectwise
family of cochain-level injective resolutions.  Under enough injectives, the stronger
source-definedness conclusion is registered globally; its objectwise and pointwise consequences
then follow from the canonical forgetful instances.  Mathlib's pointwise-to-total instance supplies
the total right derived functor automatically.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.KInjective.Bounded

variable {A : Type u₁} {D : Type u₂}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} D]

/-- Stacks 05TI: if every bounded-below cochain complex admits an injective
resolution, then the right-derived indexing diagrams of a functor out of `K⁺(A)`
are essentially constant everywhere. -/
@[stacks 05TI "objectwise-resolution globalization"]
theorem everywhereDefinedOfResolutions
    (T : HomotopyCategory.Plus A ⥤ D)
    (h_resolution : ∀ K : CochainComplex.Plus A,
      Nonempty (CochainComplex.InjectiveResolution K.obj)) :
    RightDerived.EverywhereDefined T (HomotopyCategory.Plus.quasiIso A) := sorry

/-- Stacks 05TI: the everywhere-definedness criterion supplies a pointwise right-derived
functor at quasi-isomorphisms. -/
@[stacks 05TI "objectwise-resolution globalization"]
theorem hasPointwiseOfResolutions
    (T : HomotopyCategory.Plus A ⥤ D)
    (h_resolution : ∀ K : CochainComplex.Plus A,
      Nonempty (CochainComplex.InjectiveResolution K.obj)) :
    T.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A) := sorry

/-- Stacks 05TI: enough injectives make the right-derived indexing diagram of every functor out
of `K⁺(A)` essentially constant at every source object. -/
@[stacks 05TI "enough-injectives globalization"]
instance everywhereDefinedOfEnoughInjectives
    [EnoughInjectives A] (T : HomotopyCategory.Plus A ⥤ D) :
    RightDerived.EverywhereDefined T (HomotopyCategory.Plus.quasiIso A) := sorry

/-- If every bounded-below cochain complex admits an injective resolution, the right-derived
indexing diagram is essentially constant at every object.  This retains the source-definedness
data forgotten by `HasPointwiseRightDerivedFunctor`. -/
@[stacks 05TI "objectwise-resolution source-definedness"]
theorem definedAtOfResolutions
    (T : HomotopyCategory.Plus A ⥤ D)
    (h_resolution : ∀ K : CochainComplex.Plus A,
      Nonempty (CochainComplex.InjectiveResolution K.obj))
    (X : HomotopyCategory.Plus A) :
    RightDerived.DefinedAt T (HomotopyCategory.Plus.quasiIso A) X := sorry

section Checks

variable [EnoughInjectives A] (T : HomotopyCategory.Plus A ⥤ D)
  (X : HomotopyCategory.Plus A)

/- Enough injectives canonically supply global source-definedness. -/
#synth RightDerived.EverywhereDefined T (HomotopyCategory.Plus.quasiIso A)

/- Objectwise source-definedness is inherited from the global instance. -/
#synth RightDerived.DefinedAt T (HomotopyCategory.Plus.quasiIso A) X

/- Mathlib's injective derivability structure supplies the canonical pointwise instance under
enough injectives. -/

/- The canonical pointwise instance induces the total right-derived-functor instance. -/

end Checks

end CategoryTheory.Functor.KInjective.Bounded
