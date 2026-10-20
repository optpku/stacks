module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.45.5

Pseudo-coherence under the canonical structure-sheaf derived tensor product is owned in
`RingedSite.Hom.ModuleDerived`.  This source entry checks both clauses of the Stacks lemma against
that shared API.
-/

open CategoryTheory RingedSite.Hom
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

-- Local instance justification (defeq pin): use the standard derived category and canonical
-- totalization of the structure-sheaf module tensor, matching the shared owner.
attribute [local instance] HasDerivedCategory.standard
  RingedSite.Hom.moduleCat_hasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

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

/- Lemma 21.45.5 (1) (09J9): bounded pseudo-coherence degrees add under derived tensor product. -/
@[stacks 09J9 "(1)"]
#check (RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.tensor :
  ∀ {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {n m a b : ℤ},
    K.IsMPseudoCoherent n → K.IsLE a → L.IsMPseudoCoherent m → L.IsLE b →
      RingedSite.Hom.ModuleDerived.IsMPseudoCoherent (K ⊗ᴸ L) (max (m + a) (n + b)))

/- Lemma 21.45.5 (2) (09J9): the derived tensor product of pseudo-coherent objects is
pseudo-coherent. -/
@[stacks 09J9 "(2)"]
#check (RingedSite.Hom.ModuleDerived.IsPseudoCoherent.tensor :
  ∀ {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)},
    K.IsPseudoCoherent → L.IsPseudoCoherent → RingedSite.Hom.ModuleDerived.IsPseudoCoherent (K ⊗ᴸ L))

end
