/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.SmallHom.Grothendieck
public import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import Mathlib.Algebra.Category.ModuleCat.AB
import StacksCheckRecall

@[expose] public section

/-!
# Small Hom Types in Grothendieck Derived Categories

The replacement-independent small-Hom API is owned by ReasLib.  This file records the source
remark as a typed check.
-/

open CategoryTheory Localization ComplexShape

universe t w v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

section KInjectiveComputation

variable [HasDerivedCategory.{t} A]
variable (K : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective]

/- Remark 19.13.3: a K-injective target computes morphisms in the localization of the homotopy
category at quasi-isomorphisms. -/
@[stacks 079Q "K-injective computation"] #check
  (CochainComplex.IsKInjective.homEquiv
      (MorphismProperty.Q (HomotopyCategory.quasiIso A (up ℤ))) K I :
    (K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) ≃
      ((MorphismProperty.Q (HomotopyCategory.quasiIso A (up ℤ))).obj K ⟶
        (MorphismProperty.Q (HomotopyCategory.quasiIso A (up ℤ))).obj
          ((HomotopyCategory.quotient A (up ℤ)).obj I)))

variable (N : HomotopyCategory A (up ℤ))
  (i : N ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I)
  (hi : HomotopyCategory.quasiIso A (up ℤ) i)

/- Remark 19.13.3: after choosing a quasi-isomorphism from `N` to the K-injective target `I`,
homotopy morphisms into `I` compute localized morphisms into the original target `N`. -/
@[stacks 079Q "K-injective replacement"] #check
  (CochainComplex.IsKInjective.Replacement.homEquiv
      (MorphismProperty.Q (HomotopyCategory.quasiIso A (up ℤ))) K N I i hi :
    (K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) ≃
      ((MorphismProperty.Q (HomotopyCategory.quasiIso A (up ℤ))).obj K ⟶
        (MorphismProperty.Q (HomotopyCategory.quasiIso A (up ℤ))).obj N))

end KInjectiveComputation

/- Remark 19.13.3: for a Grothendieck abelian category, the resulting localized Hom types are
small. -/
@[stacks 079Q "small localized Hom"] #check
  (DerivedCategory.HomotopyLocalizedHom.of_grothendieck :
    ∀ K L : HomotopyCategory A (up ℤ),
      HasSmallLocalizedHom.{w} (HomotopyCategory.quasiIso A (up ℤ)) K L)

#check @CochainComplex.IsKInjective.homEquiv_apply
#check @CochainComplex.IsKInjective.homEquiv_naturality_left
#check @CochainComplex.IsKInjective.homEquiv_naturality_right
#check @CochainComplex.IsKInjective.Replacement.homEquiv_apply
#check @CochainComplex.IsKInjective.Replacement.homEquiv_naturality_left

section Examples

/- Remark 19.13.3: module categories are Grothendieck abelian, hence their derived localized
Hom types are small by the preceding general theorem. -/
@[stacks 079Q "module-category example"] #check
  fun (R : Type u) [Ring R] ↦
    (inferInstance : IsGrothendieckAbelian.{u} (ModuleCat.{u} R))

/- Remark 19.13.3: sheaves of modules on a ringed site are Grothendieck abelian under the
standard sheafification hypotheses. -/
@[stacks 079Q "sheaf-module example"] #check
  fun (C : Type u) [Category.{max u v} C] (J : GrothendieckTopology C)
      [HasSheafify J AddCommGrpCat.{max u v}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
      (𝒪 : Sheaf J RingCat.{max u v}) ↦
    (inferInstance : IsGrothendieckAbelian.{max u v}
      (SheafOfModules.{max u v} 𝒪))

end Examples

end CategoryTheory
