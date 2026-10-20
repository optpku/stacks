/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.Snake
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Milnor consequences for short exact systems of modules

This leaf exposes the module-valued form of the standard Milnor consequence: if the left term of
a short exact sequential row is Mittag-Leffler, the induced map on canonical first derived
limits is an isomorphism. The inverse is constructed explicitly by lifting along the
epimorphic product map and projecting to the Milnor cokernel.
@stack 0H31
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.ShortExact

variable {R : Type u} [Ring R]

/-- The product of the stagewise right maps of a short exact sequential row is epimorphic. -/
@[stacks 0H31 "epimorphic right map of the Milnor product row"]
theorem productMap_g_epi
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) :
    Epi (SequentialInverseSystem.productMap S.g) := sorry

/-- When the left term is Mittag-Leffler, the kernel of the product map `∏ S.X₂ ⟶ ∏ S.X₃`
dies in the first derived limit of `S.X₂`: it is the image of `∏ S.X₁`, whose first derived
limit vanishes. -/
@[stacks 0H31 "product kernel vanishes in the first derived limit"]
theorem kernel_ι_productMap_g_comp_π
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    kernel.ι (SequentialInverseSystem.productMap S.g) ≫
        SequentialInverseSystem.Milnor.ProductCone.canonicalR1.π S.X₂ = 0 := sorry

/-- The map `∏ S.X₃ ⟶ R¹ lim S.X₂` obtained by lifting along the epimorphic product map
`∏ S.X₂ ⟶ ∏ S.X₃` and projecting to the Milnor cokernel of `S.X₂`. -/
@[stacks 0H31 "lift of the Milnor quotient along the product row"]
noncomputable def productToFirstDerivedLimit
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    ∏ᶜ S.X₃.family ⟶ S.X₂.firstDerivedLimit :=
  -- Local instance justification (proof-local temporary data): the epimorphism is the explicit
  -- certificate `productMap_g_epi hS`; descent uses mathlib's cokernel-of-kernel presentation.
  letI := productMap_g_epi hS
  Abelian.epiDesc (SequentialInverseSystem.productMap S.g)
    (SequentialInverseSystem.Milnor.ProductCone.canonicalR1.π S.X₂)
    (kernel_ι_productMap_g_comp_π hS hX₁)

/-- The lifted Milnor quotient annihilates the Milnor difference map of `S.X₃`. -/
theorem milnorDifferenceMap_comp_productToFirstDerivedLimit
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    S.X₃.milnorDifferenceMap ≫ productToFirstDerivedLimit hS hX₁ = 0 := sorry

/-- The inverse comparison `R¹ lim S.X₃ ⟶ R¹ lim S.X₂`: a class represented by `y ∈ ∏ S.X₃`
is sent to the class of any lift of `y` to `∏ S.X₂`. -/
@[stacks 0H31 "inverse first derived limit comparison after a Mittag-Leffler term"]
noncomputable def firstDerivedLimitInv
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    S.X₃.firstDerivedLimit ⟶ S.X₂.firstDerivedLimit :=
  SequentialInverseSystem.Milnor.ProductCone.canonicalR1.desc S.X₃
    (productToFirstDerivedLimit hS hX₁)
    (milnorDifferenceMap_comp_productToFirstDerivedLimit hS hX₁)

/-- The induced map followed by the explicit inverse is the identity of `R¹ lim S.X₂`. -/
theorem firstDerivedLimitMap_comp_firstDerivedLimitInv
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    SequentialInverseSystem.firstDerivedLimitMap S.g ≫ firstDerivedLimitInv hS hX₁ =
      𝟙 S.X₂.firstDerivedLimit := sorry

/-- The explicit inverse followed by the induced map is the identity of `R¹ lim S.X₃`. -/
theorem firstDerivedLimitInv_comp_firstDerivedLimitMap
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    firstDerivedLimitInv hS hX₁ ≫ SequentialInverseSystem.firstDerivedLimitMap S.g =
      𝟙 S.X₃.firstDerivedLimit := sorry

/-- The isomorphism on canonical first derived limits induced by the right map of a short exact
row with Mittag-Leffler left term, with the explicit inverse `firstDerivedLimitInv`. -/
@[stacks 0H31 "first derived limit isomorphism after a Mittag-Leffler term"]
noncomputable def firstDerivedLimitIso
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    S.X₂.firstDerivedLimit ≅ S.X₃.firstDerivedLimit where
  hom := SequentialInverseSystem.firstDerivedLimitMap S.g
  inv := firstDerivedLimitInv hS hX₁
  hom_inv_id := firstDerivedLimitMap_comp_firstDerivedLimitInv hS hX₁
  inv_hom_id := firstDerivedLimitInv_comp_firstDerivedLimitMap hS hX₁

/-- In a short exact row of sequential modules with Mittag-Leffler left term, the map from the
middle to the right canonical first derived limit is an isomorphism. -/
@[stacks 0H31 "first derived limit after a Mittag-Leffler term"]
theorem firstDerivedLimitMap_isIso
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    IsIso (SequentialInverseSystem.firstDerivedLimitMap S.g) :=
  (firstDerivedLimitIso hS hX₁).isIso_hom

end CategoryTheory.ModuleCat.ShortExact
