/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Remark_91_4_5_Equivalence
public import stacks_project.Chap91.Remark_91_4_5_OfModule
public import stacks_project.Chap91.Remark_91_4_5_Trivialization
import StacksCheckRecall

open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Remark 91.4.5 (1) A first-order thickening i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'}) is trivial if
there exists a morphism of ringed spaces π : X' ⟶ X which is a left inverse to i. -/
@[stacks 08L9] #check
  (@AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.IsTrivial :
    {X X' : AlgebraicGeometry.RingedSpace.{u}} →
      (i : X ⟶ X') →
      IsFirstOrderThickening i → Prop)

/- Remark 91.4.5 (2) The choice of such a morphism π is called a trivialization of the
first-order thickening. -/
@[stacks 08L9] #check
  (@AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Trivialization :
    ∀ {X X' : AlgebraicGeometry.RingedSpace.{u}} (i : X ⟶ X')
      [h : IsFirstOrderThickening i], Type u)

/- Remark 91.4.5 (3) Given π we obtain a splitting 𝒪_{X'} = 𝒪_X ⊕ ℐ as sheaves of algebras
on X by using π^♯ to split the surjection 𝒪_{X'} ⟶ 𝒪_X. Conversely, such a splitting
determines a morphism π. -/
@[stacks 08L9] #check
  (@AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.ofSplitting)
@[stacks 08L9] #check
  (@AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.splittingIso)

/- Remark 91.4.5 (4) The category of trivialized first-order thickenings of (X, 𝒪_X) is
equivalent to the category of 𝒪_X-modules. Formally this is the opposite equivalence
Trivialized X ≌ (X.Modules)ᵒᵖ, matching the variance of kernel-ideal maps. -/
@[stacks 08L9] #check
  (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.modulesEquiv :
    (X : AlgebraicGeometry.RingedSpace.{u}) →
      AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Trivialized X ≌
        (X.Modules)ᵒᵖ)
