/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor

/-!
# Pseudo-coherent derived tensor products on ringed sites

Pseudo-coherence is stable under the derived tensor product over the commutative structure
sheaf. The ordinary tensor is fixed by the ring-sheaf presentation; only the existence of its
fixed-right derived functors is an explicit input.
-/

@[expose] public section

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] HasDerivedCategory.standard
  RingedSite.Hom.moduleCat_hasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  HasWeakSheafify ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology
    AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O)]

/-- Lemma 21.45.5 (1): if `K` is `n`-pseudo-coherent and lies in `D^{≤ a}`, while `L` is
`m`-pseudo-coherent and lies in `D^{≤ b}`, then `K ⊗ᴸ L` is
`max (m + a) (n + b)`-pseudo-coherent. -/
@[stacks 09J9 "(1)"]
theorem IsMPseudoCoherent.tensor
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {n m a b : ℤ}
    (hK : K.IsMPseudoCoherent n) (hKLE : K.IsLE a)
    (hL : L.IsMPseudoCoherent m) (hLLE : L.IsLE b) :
    IsMPseudoCoherent (X := RingedSite.ofCommRingSheaf J O) (K ⊗ᴸ L) (max (m + a) (n + b)) := sorry

/-- Lemma 21.45.5 (2): the derived tensor product of two pseudo-coherent objects over `O` is
pseudo-coherent. -/
@[stacks 09J9 "(2)"]
theorem IsPseudoCoherent.tensor
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : K.IsPseudoCoherent) (hL : L.IsPseudoCoherent) :
    IsPseudoCoherent (X := RingedSite.ofCommRingSheaf J O) (K ⊗ᴸ L) := sorry

end

end RingedSite.Hom.ModuleDerived
