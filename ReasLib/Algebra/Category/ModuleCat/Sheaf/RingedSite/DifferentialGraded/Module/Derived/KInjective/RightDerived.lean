/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Basic
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt

/-!
# Right-derived computation from DG K-injectives

Exact functors on the intrinsic DG homotopy category admit right-derived extensions along
DG quasi-isomorphisms.  A represented DG module which is both graded-injective and K-injective
computes that extension at its homotopy object.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v uD vD

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Functor.RightDerived

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))

variable {𝒟 : Type uD} [Category.{vD} 𝒟]
variable [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [Preadditive 𝒟]
variable [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
variable [Pretriangulated 𝒟] [IsTriangulated 𝒟]
variable (T : K ℤ Mod(𝒜, d) ⥤ 𝒟) [T.CommShift ℤ] [T.IsTriangulated]

/-- Stacks 0FTN: every exact functor from the intrinsic DG homotopy category has a right-derived
extension along DG quasi-isomorphisms. -/
@[stacks 0FTN]
theorem exists_of_exact :
    T.HasRightDerivedFunctor (Homotopy.quasiIso 𝒜) := sorry

/-- The canonical right-derivability instance supplied by K-injective resolutions. -/
@[stacks 0FTN "right derivability from DG K-injectives"]
instance hasRightDerivedFunctor :
    T.HasRightDerivedFunctor (Homotopy.quasiIso 𝒜) :=
  exists_of_exact 𝒜 T

/-- The chosen total right-derived extension of an exact functor on the intrinsic DG homotopy
category. -/
@[stacks 0FTP "total right-derived functor on DG module sheaves"]
noncomputable def functor : DerivedCategory 𝒜 ⥤ 𝒟 :=
  T.totalRightDerived (DerivedCategory.Qh 𝒜) (Homotopy.quasiIso 𝒜)

/-- The canonical comparison from an exact homotopy-level functor to its total right-derived
extension. -/
@[stacks 0FTP "unit of the total right-derived functor"]
noncomputable def unit :
    T ⟶ DerivedCategory.Qh 𝒜 ⋙ functor 𝒜 T :=
  T.totalRightDerivedUnit (DerivedCategory.Qh 𝒜) (Homotopy.quasiIso 𝒜)

/-- The chosen extension and its comparison unit satisfy the right-derived universal property. -/
@[stacks 0FTN "universal property of the DG right-derived functor"]
theorem isRightDerived :
    (functor 𝒜 T).IsRightDerivedFunctor (unit 𝒜 T) (Homotopy.quasiIso 𝒜) := sorry

/-- Stacks 0FTN: a DG module which is graded-injective and K-injective computes the right-derived
extension of `T` at its intrinsic homotopy object. -/
@[stacks 0FTN]
theorem computesAt_of_gradedInjective
    (I : Mod(𝒜, d)) [Module.IsKInjective.GradedInjective I] :
    CategoryTheory.Functor.RightDerived.ComputesAt
      T (Homotopy.quasiIso 𝒜) ((toK 𝒜).obj I) := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Functor.RightDerived
