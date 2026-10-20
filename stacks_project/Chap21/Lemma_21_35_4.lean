module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Monoidal.Closed.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Derived sheaf internal Hom preserves triangles in both variables

The source-facing checks use the actual sheaf-valued derived bifunctor and its concrete
K-injective-model shift comparisons. The output is D(𝒪), and no chosen monoidal/closed
structure or tensor-compatibility premise on the derived category is supplied by the caller.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Pretriangulated.Opposite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (K L : RingedSiteDerived.max J 𝒪)

/- Lemma 21.35.4 (08JC), target variable: the actual RSheafHom(K,-) commutes with shifts. -/
@[stacks 08JC "actual sheaf-valued target-variable shifts"]
#check (inferInstance :
  (_root_.RingedSite.Hom.ModuleDerived.InternalHom.targetFunctor K).CommShift ℤ)

/- Lemma 21.35.4 (08JC), target variable: the actual RSheafHom(K,-) preserves triangles. -/
@[stacks 08JC "actual sheaf-valued target-variable distinguished triangles"]
#check (inferInstance :
  (_root_.RingedSite.Hom.ModuleDerived.InternalHom.targetFunctor K).IsTriangulated)

/- Lemma 21.35.4 (08JC), source variable: the actual RSheafHom(-,L) has negative-source shifts. -/
@[stacks 08JC "actual sheaf-valued source-variable shifts"]
#check (inferInstance :
  (_root_.RingedSite.Hom.ModuleDerived.InternalHom.sourceFunctor L).CommShift ℤ)

/- Lemma 21.35.4 (08JC), source variable: the actual RSheafHom(-,L) preserves triangles. -/
@[stacks 08JC "actual sheaf-valued source-variable distinguished triangles"]
#check (inferInstance :
  (_root_.RingedSite.Hom.ModuleDerived.InternalHom.sourceFunctor L).IsTriangulated)

/- Retain the generic canonical-reuse entry points for chapter clients. -/
#check @CategoryTheory.MonoidalClosed.ihom_commShift_of_tensorLeft
#check @CategoryTheory.MonoidalClosed.ihom_isTriangulated_of_tensorLeft
#check @CategoryTheory.MonoidalClosed.internalHomFlip_commShift_of_tensorRight
#check @CategoryTheory.MonoidalClosed.internalHomFlip_isTriangulated_of_tensorRight

end SheafOfModules.RingedSite
