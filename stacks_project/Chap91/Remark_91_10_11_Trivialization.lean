/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Quotient
public import stacks_project.Chap91.Remark_91_10_10_Thickening

/-!
# Canonical trivialization of a complex of first-order thickenings

A complex of same-site first-order thickenings determines a unique section of the first
thickening, obtained by eliminating `ker π3` and lifting the composite ring-sheaf map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 𝒪1 𝒪2 𝒪3 : Sheaf J CommRingCat.{max u v}}
variable {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪} {π3 : 𝒪3 ⟶ 𝒪}
variable [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
variable [IsFirstOrderThickening π3]

/-- The kernel of `π3` is contained in the kernel of the composite `𝒪'₃ ⟶ 𝒪'₁`
of a complex of first-order thickenings. -/
theorem isComplex_kernel_le (f : Hom π1 π2) (g : Hom π2 π3) (hC : IsComplex f g) :
    KernelIdeal.subobject π3 ≤ KernelIdeal.subobject (g.hom ≫ f.hom) := sorry

/-- The canonical splitting `𝒪 ⟶ 𝒪'₁` of a complex of first-order thickenings,
obtained by eliminating `ker π3` and lifting the composite `𝒪'₃ ⟶ 𝒪'₁`. -/
noncomputable def canonicalTrivialization (f : Hom π1 π2) (g : Hom π2 π3)
    (hC : IsComplex f g) : 𝒪 ⟶ 𝒪1 :=
  (KernelIdeal.quotientIso π3 (KernelIdeal.quotientComparison_isIso π3)).inv ≫
    IdealSheaf.Quotient.lift (KernelIdeal.subobject π3) (g.hom ≫ f.hom)
      (isComplex_kernel_le f g hC)

/-- The canonical trivialization is a section of `π1`. -/
theorem canonicalTrivialization_isTrivialization (f : Hom π1 π2) (g : Hom π2 π3)
    (hC : IsComplex f g) :
    IsTrivialization (canonicalTrivialization f g hC) π1 := sorry

/-- The composite `𝒪'₃ ⟶ 𝒪'₁` factors through `π3` as
`π3 ≫ canonicalTrivialization`. -/
theorem canonicalTrivialization_comp (f : Hom π1 π2) (g : Hom π2 π3)
    (hC : IsComplex f g) :
    g.hom ≫ f.hom = π3 ≫ canonicalTrivialization f g hC := sorry

/-- The canonical trivialization is the unique section of `π1` through which the
composite `𝒪'₃ ⟶ 𝒪'₁` factors. -/
theorem canonicalTrivialization_unique (f : Hom π1 π2) (g : Hom π2 π3)
    (hC : IsComplex f g) {σ : 𝒪 ⟶ 𝒪1} (hσ : IsTrivialization σ π1)
    (hcomp : g.hom ≫ f.hom = π3 ≫ σ) :
    σ = canonicalTrivialization f g hC := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
