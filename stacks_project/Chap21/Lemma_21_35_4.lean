module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Monoidal.Closed.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.4

The source assertion that derived internal Hom is exact in either variable is the specialization
of the fixed-factor adjoint API.  The chapter records the four fine-grained structures separately;
later users can provide exactness for only the tensor factors they need.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open scoped Pretriangulated.Opposite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]
variable [HasZeroObject (RingedSiteDerived J 𝒪)]
variable [Preadditive (RingedSiteDerived J 𝒪)]
variable [HasShift (RingedSiteDerived J 𝒪) ℤ]
variable [∀ n : ℤ, (shiftFunctor (RingedSiteDerived J 𝒪) n).Additive]
variable [Pretriangulated (RingedSiteDerived J 𝒪)]

variable (K L : RingedSiteDerived J 𝒪)
variable [hK : (tensorLeft K).CommShift ℤ]
variable [hKTri : (tensorLeft K).IsTriangulated]
variable [hL : ((tensoringRight (RingedSiteDerived J 𝒪)).obj L).CommShift ℤ]

/- Lemma 21.35.4 (08JC), target variable: `RHom(K, -)` commutes with shift. -/
@[stacks 08JC "internal-Hom target-variable shift compatibility"] #check
  (CategoryTheory.MonoidalClosed.ihom_commShift_of_tensorLeft K)

/- Lemma 21.35.4 (08JC), target variable: `RHom(K, -)` is triangulated. -/
@[stacks 08JC "internal-Hom target-variable exactness"] #check
  (CategoryTheory.MonoidalClosed.ihom_isTriangulated_of_tensorLeft K)

/- Lemma 21.35.4 (08JC), source variable: `RHom(-, L)` commutes with shift. -/
@[stacks 08JC "internal-Hom source-variable shift compatibility"] #check
  (CategoryTheory.MonoidalClosed.internalHomFlip_commShift_of_tensorRight L)

/- Lemma 21.35.4 (08JC), source variable: `RHom(-, L)` is triangulated. -/
@[stacks 08JC "internal-Hom source-variable exactness"] #check
  @CategoryTheory.MonoidalClosed.internalHomFlip_isTriangulated_of_tensorRight

end

end SheafOfModules.RingedSite
