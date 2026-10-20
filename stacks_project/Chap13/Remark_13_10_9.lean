/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒞]
  [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts ℬ] [HasBinaryBiproducts 𝒞]
  [HasZeroObject 𝒜] [HasZeroObject ℬ] [HasZeroObject 𝒞]

variable (tensor : 𝒜 ⥤ ℬ ⥤ 𝒞) [tensor.Additive] [∀ X : 𝒜, (tensor.obj X).Additive]
variable [∀ (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ),
  CochainComplex.HasMapBifunctor X Y tensor]
variable (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ)

/- Remark 13.10.9 (1): after fixing the left cochain-complex factor, bifunctor totalization
commutes with shifts and is an exact functor on homotopy categories. -/
#check (inferInstance :
  (Functor.Homotopy.BifunctorTotal.leftFixed tensor X).CommShift ℤ)
@[stacks 0G6E "exactness of left fixed-factor bifunctor totalization"] #check (inferInstance :
  (Functor.Homotopy.BifunctorTotal.leftFixed tensor X).IsTriangulated)

/- Remark 13.10.9 (2): after fixing the right cochain-complex factor, bifunctor totalization
commutes with shifts and is an exact functor on homotopy categories. -/
#check (inferInstance :
  (Functor.Homotopy.BifunctorTotal.rightFixed tensor Y).CommShift ℤ)
@[stacks 0G6E "exactness of right fixed-factor bifunctor totalization"] #check (inferInstance :
  (Functor.Homotopy.BifunctorTotal.rightFixed tensor Y).IsTriangulated)

#check @Functor.Homotopy.BifunctorTotal.leftFixed
#check @Functor.Homotopy.BifunctorTotal.rightFixed
