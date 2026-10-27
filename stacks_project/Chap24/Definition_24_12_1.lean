/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Transport
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable (A B : DGA(𝒪))

/- Definition 24.12.1 (1): a sheaf of differential graded 𝒪-algebras on a ringed site
(C, 𝒪) is a cochain complex of 𝒪-modules with associative unital 𝒪-bilinear
multiplication maps A n × A m ⟶ A (n + m) satisfying the graded Leibniz rule. -/
@[stacks 0FRF] #check
  (SheafOfModules.RingedSite.DifferentialGradedAlgebra (𝒪 := 𝒪) : Type (max u v (w + 1)))

/- Definition 24.12.1 (2): a homomorphism of differential graded 𝒪-algebras is a
map of complexes of 𝒪-modules compatible with the multiplication maps.
Unit-preserving homomorphisms are denoted by DifferentialGradedAlgebra.Hom. -/
@[stacks 0FRF] #check
  (SheafOfModules.RingedSite.DifferentialGradedAlgebra.MulHom A B : Type (max u w))
