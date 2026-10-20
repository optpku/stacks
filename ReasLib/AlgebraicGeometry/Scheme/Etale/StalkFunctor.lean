/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisModule

@[expose] public section

open CategoryTheory
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry

noncomputable section

universe u

namespace GaloisCohomology

/-- Naturality of the additive stalk map is equivariant for the Galois action. -/
theorem etaleStalkFunctor_map_comm (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (f : F ⟶ G) :
    ∀ (g : Gal(Ksep / K)),
      (etaleStalk K Ksep F).obj.ρ g ≫
          ModuleCat.ofHom
            (((etalePoint K Ksep).sheafFiber.map f).hom.toIntLinearMap) =
        ModuleCat.ofHom
            (((etalePoint K Ksep).sheafFiber.map f).hom.toIntLinearMap) ≫
          (etaleStalk K Ksep G).obj.ρ g := sorry

/-- The additive stalk map induced by a morphism of étale sheaves. -/
def etaleStalkMap (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (f : F ⟶ G) : etaleStalk K Ksep F ⟶ etaleStalk K Ksep G :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        (((etalePoint K Ksep).sheafFiber.map f).hom.toIntLinearMap)
      comm := etaleStalkFunctor_map_comm K Ksep f }

/-- The additive stalk map preserves identities. -/
theorem etaleStalkFunctor_map_id (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    etaleStalkMap K Ksep (𝟙 F) = 𝟙 (etaleStalk K Ksep F) := sorry

/-- The additive stalk map preserves compositions. -/
theorem etaleStalkFunctor_map_comp (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    {F G H : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (f : F ⟶ G) (g : G ⟶ H) :
    etaleStalkMap K Ksep (f ≫ g) =
      etaleStalkMap K Ksep f ≫ etaleStalkMap K Ksep g := sorry

/-- The additive étale stalk functor associated with a chosen separable closure. -/
def etaleStalkFunctor (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      DiscreteModuleCat ℤ (Gal(Ksep / K)) where
  obj F := etaleStalk K Ksep F
  map := etaleStalkMap K Ksep
  map_id := etaleStalkFunctor_map_id K Ksep
  map_comp := etaleStalkFunctor_map_comp K Ksep

/-- The additive étale stalk functor is an unconditional equivalence. -/
instance etaleStalkFunctorIsEquivalence (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] :
    (etaleStalkFunctor K Ksep).IsEquivalence := sorry

end GaloisCohomology

end
