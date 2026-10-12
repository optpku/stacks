/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.ModuleTensor
import StacksCheckRecall

/-! @stack 07MB -/

@[expose] public section

/-
20.25.3.2 (07MB):

`Tot (Tot (Cech 𝒰 F) ⊗[ℤ] Tot (Cech 𝒰 G)) ⟶
  Tot (Cech 𝒰 (Tot (F ⊗[ℤ] G)))`.

The main owner uses the genuine universe-polymorphic tensor bifunctor on `ModuleCat ℤ`.  Its
generic layer keeps the coefficient bifunctor explicit, assembles the four homogeneous degrees
with the Koszul cross sign, and therefore does not identify tensor product with the Cartesian
monoidal structure on additive groups.
-/
@[stacks 07MB "canonical Cech tensor comparison"]
#check CategoryTheory.Cech.ModuleTensor.comparison (R := ℤ)

#check @CategoryTheory.Cech.ModuleTensor.comparison_naturality
#check @CategoryTheory.Cech.ModuleTensor.comparison_f
#check @CategoryTheory.Cech.ModuleTensor.pairing
#check @CategoryTheory.Cech.ModuleTensor.pairing_f

#check @CategoryTheory.Cech.Bifunctor.Total.comparison
#check @CategoryTheory.Cech.Bifunctor.Total.component
#check @CategoryTheory.Cech.Bifunctor.Total.comparison_naturality
#check @CategoryTheory.Cech.Bifunctor.rowComparisonZ
#check @ComplexShape.Embedding.extendBifunctorHom

end
