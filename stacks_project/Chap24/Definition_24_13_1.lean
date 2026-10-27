/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.GradedObject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Regular
import StacksCheckRecall

@[expose] public section

/-!
# Definition 24.13.1

Right differential graded modules over a sheaf of DG algebras, their homomorphisms, and the
named category `Mod(𝒜, d)` are owned by `DifferentialGradedModule`, `Hom`, and `moduleCategory`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable (𝒜 : DGA(𝒪))
variable (M N : SheafOfModules.RingedSite.DifferentialGradedModule 𝒜)

/- Definition 24.13.1 (1): a right differential graded module over a sheaf of DG algebras is a
cochain complex of `𝒪`-modules with `𝒪`-bilinear right multiplications that are associative,
unital, and Leibniz. -/
@[stacks 0FRI] #check
  (SheafOfModules.RingedSite.DifferentialGradedModule 𝒜 : Type (max u v (w + 1)))

/- Definition 24.13.1 (2): a homomorphism of differential graded `𝒜`-modules is a map of complexes
of `𝒪`-modules compatible with multiplication. -/
@[stacks 0FRI] #check
  (SheafOfModules.RingedSite.DifferentialGradedModule.Hom M N : Type (max u w))

/- Definition 24.13.1 (3): the category of right differential graded `𝒜`-modules is denoted
`Mod(𝒜, d)`. -/
@[stacks 0FRI] #check
  (SheafOfModules.RingedSite.DifferentialGradedModule.moduleCategory 𝒜 :
    Type (max u v (w + 1)))
#check
  (SheafOfModules.RingedSite.DifferentialGradedModule.instCategory 𝒜 :
    Category.{max u w}
      (SheafOfModules.RingedSite.DifferentialGradedModule.moduleCategory 𝒜))

#check
  (SheafOfModules.RingedSite.DifferentialGradedModule.toGradedObject M :
    GradedObject ℤ (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J 𝒪))


