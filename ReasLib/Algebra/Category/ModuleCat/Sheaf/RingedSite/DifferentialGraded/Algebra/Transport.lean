/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra

/-!
# Computation laws for transport of differential graded algebra sheaves

The underlying complex, unit, and multiplication of a differential graded algebra structure
transported along an isomorphism of cochain complexes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

/-- The underlying complex of a transported differential graded algebra is the target complex. -/
@[simp]
theorem transport_toComplex (A : DifferentialGradedAlgebra (𝒪 := 𝒪))
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (e : A.toComplex ≅ K) : (transport A K e).toComplex = K := rfl

/-- The unit of a transported differential graded algebra is the image of its original unit. -/
@[simp]
theorem transport_one (A : DifferentialGradedAlgebra (𝒪 := 𝒪))
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (e : A.toComplex ≅ K) : (transport A K e).one = A.one ≫ e.hom.f 0 := rfl

/-- Transported homogeneous multiplication is conjugation by the components of the complex
isomorphism. -/
@[simp]
theorem transport_mul (A : DifferentialGradedAlgebra (𝒪 := 𝒪))
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (e : A.toComplex ≅ K) (n m : ℤ) :
    (transport A K e).mul n m =
      (e.inv.f n ⊗ₘ e.inv.f m) ≫ A.mul n m ≫ e.hom.f (n + m) := rfl

end SheafOfModules.RingedSite.DifferentialGradedAlgebra

end
