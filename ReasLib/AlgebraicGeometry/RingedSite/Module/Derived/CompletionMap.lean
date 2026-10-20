/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness

@[expose] public section

open CategoryTheory SheafOfModules.RingedSite

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}]

/-- A morphism is a derived completion map with respect to `I` when its target is
derived complete and precomposition induces a bijection to every derived-complete target. -/
def IsDerivedCompletion (I : Subobject (unitModule J O))
    {K Khat : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)} (η : K ⟶ Khat) : Prop :=
  IsDerivedCompleteWithRespectTo Khat I ∧
    ∀ (L : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)),
      IsDerivedCompleteWithRespectTo L I →
        Function.Bijective (fun g : Khat ⟶ L ↦ η ≫ g)

/-- A derived completion map has a derived-complete target. -/
theorem IsDerivedCompletion.complete (I : Subobject (unitModule J O))
    {K Khat : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)} {η : K ⟶ Khat}
    (hη : IsDerivedCompletion I η) : IsDerivedCompleteWithRespectTo Khat I := sorry

/-- The defining completeness and universal mapping properties of a derived completion map. -/
theorem isDerivedCompletion_iff (I : Subobject (unitModule J O))
    {K Khat : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)} (η : K ⟶ Khat) :
    IsDerivedCompletion I η ↔
      IsDerivedCompleteWithRespectTo Khat I ∧
        ∀ (L : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)),
          IsDerivedCompleteWithRespectTo L I →
            Function.Bijective (fun g : Khat ⟶ L ↦ η ≫ g) := sorry

namespace IsDerivedCompletion

/-- Precomposition with a derived completion map gives the universal hom-set equivalence. -/
noncomputable def homEquiv (I : Subobject (unitModule J O))
    {K Khat : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)} {η : K ⟶ Khat}
    (hη : IsDerivedCompletion I η)
    {L : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)}
    (hL : IsDerivedCompleteWithRespectTo L I) : (Khat ⟶ L) ≃ (K ⟶ L) :=
  Equiv.ofBijective (fun g : Khat ⟶ L ↦ η ≫ g) (hη.2 L hL)

/-- The universal hom-set equivalence acts by precomposition with the completion map. -/
theorem homEquiv_apply (I : Subobject (unitModule J O))
    {K Khat : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)} {η : K ⟶ Khat}
    (hη : IsDerivedCompletion I η)
    {L : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)}
    (hL : IsDerivedCompleteWithRespectTo L I) (g : Khat ⟶ L) :
    homEquiv I hη hL g = η ≫ g := sorry

/-- Two derived completion targets are canonically isomorphic by their universal mapping
properties. -/
noncomputable def comparisonIso (I : Subobject (unitModule J O))
    {K Khat Khat' : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)}
    {η : K ⟶ Khat} {η' : K ⟶ Khat'}
    (hη : IsDerivedCompletion I η) (hη' : IsDerivedCompletion I η') : Khat ≅ Khat' where
  hom := (homEquiv I hη hη'.1).symm η'
  inv := (homEquiv I hη' hη.1).symm η
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical comparison from one derived completion target to another is the forward
morphism of their canonical isomorphism. -/
noncomputable abbrev comparison (I : Subobject (unitModule J O))
    {K Khat Khat' : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)}
    {η : K ⟶ Khat} {η' : K ⟶ Khat'}
    (hη : IsDerivedCompletion I η) (hη' : IsDerivedCompletion I η') : Khat ⟶ Khat' :=
  (comparisonIso I hη hη').hom

/-- The canonical comparison factors the second completion map through the first. -/
theorem comparison_fac (I : Subobject (unitModule J O))
    {K Khat Khat' : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)}
    {η : K ⟶ Khat} {η' : K ⟶ Khat'}
    (hη : IsDerivedCompletion I η) (hη' : IsDerivedCompletion I η') :
    η ≫ comparison I hη hη' = η' := sorry

end IsDerivedCompletion
end RingedSite.Hom.ModuleDerived
