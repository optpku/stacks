/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y' Y : Scheme.{u}} (f' : X ⟶ Y') (g : Y' ⟶ Y)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [LocallyQuasiFinite (f' ≫ g)] [LocallyOfFiniteType (f' ≫ g)]
variable [IsSeparated g] [LocallyOfFiniteType g]

/- Lemma 63.4.11: canonical mixed composition of finite-support and compact-support
direct image, compatible with open covariance, base change, and separated composition. -/
@[stacks 0F79] #check
  (AlgebraicGeometry.Scheme.Etale.lowerShriekCompIso :
    ∀ {X Y' Y : Scheme.{u}} (f' : X ⟶ Y') (g : Y' ⟶ Y)
      [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
      [LocallyQuasiFinite (f' ≫ g)] [LocallyOfFiniteType (f' ≫ g)]
      [IsSeparated g] [LocallyOfFiniteType g],
      lowerShriek (f' ≫ g) ≅ lowerShriek f' ⋙ etaleLowerShriek g)

section openImmersion

variable {X₁ Y₁' : Scheme.{u}} (a : X₁ ⟶ X) (f₁' : X₁ ⟶ Y₁') (j' : Y₁' ⟶ Y')
variable (h_cart : IsPullback a f₁' f' j')
variable [IsOpenImmersion a] [IsOpenImmersion j']
variable [LocallyQuasiFinite f₁'] [LocallyOfFiniteType f₁']
variable [LocallyQuasiFinite (f₁' ≫ j' ≫ g)] [LocallyOfFiniteType (f₁' ≫ j' ≫ g)]
variable [LocallyQuasiFinite (a ≫ f' ≫ g)] [LocallyOfFiniteType (a ≫ f' ≫ g)]
variable [IsSeparated (j' ≫ g)] [LocallyOfFiniteType (j' ≫ g)]

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekCompIso_openImmersion f' g a f₁' j' h_cart :
    lowerShriekCompIso_openImmersion_inner f' g a f₁' j' h_cart =
      lowerShriekCompIso_openImmersion_outer f' g a)

end openImmersion

section baseChange

variable {X₁ Y₁' Y₁ : Scheme.{u}}
variable (f₁' : X₁ ⟶ Y₁') (g₁ : Y₁' ⟶ Y₁) (b : Y₁ ⟶ Y)
variable (b' : Y₁' ⟶ Y') (a : X₁ ⟶ X)
variable (h_upper : IsPullback a f₁' f' b') (h_lower : IsPullback b' g₁ g b)
variable [LocallyQuasiFinite f₁'] [LocallyOfFiniteType f₁']
variable [LocallyQuasiFinite (f₁' ≫ g₁)] [LocallyOfFiniteType (f₁' ≫ g₁)]
variable [IsSeparated g₁] [LocallyOfFiniteType g₁]

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekCompIso_baseChange f' g f₁' g₁ b b' a h_upper h_lower :
    lowerShriekCompIso_baseChange_inner f' g f₁' g₁ b b' a h_upper h_lower =
      lowerShriekCompIso_baseChange_outer f' g f₁' g₁ b b' a h_upper h_lower)

end baseChange

section separated

variable [IsSeparated f']

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekCompIso_separated f' g :
    lowerShriekCompIso_separated_left f' g =
      lowerShriekCompIso_separated_right f' g)

end separated

end AlgebraicGeometry.Scheme.Etale

end
