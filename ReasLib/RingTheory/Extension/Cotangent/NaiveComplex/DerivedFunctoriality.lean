/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.RestrictScalars.Map
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.Embedding.Functor

/-! # Derived change of target for naive cotangent complexes -/

@[expose] public section

open CategoryTheory
open DerivedCategory HomologicalComplex ComplexShape

noncomputable section

universe u

namespace Algebra.NaiveCotangent

open Algebra.Generators

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
variable {B : Type u} [CommRing B] [Algebra Λ B]

/-- Target-changing comparison `NL{A⁄Λ} ⟶ Res_A(NL{B⁄Λ})` along a `Λ`-algebra
map `A → B`. -/
def naiveCotangentRestrictMap (φ : A →ₐ[Λ] B) :
    Algebra.naiveCotangentObject Λ A ⟶
      (ModuleCat.derivedRestrictionOfScalars φ.toRingHom).obj
        (Algebra.naiveCotangentObject Λ B) :=
  let generatorsMap :=
    @Generators.defaultHom Λ A A _ _ _ (Generators.self Λ A)
      Λ B B _ _ _ (Generators.self Λ B) φ.toRingHom.toAlgebra
  let extensionMap :=
    @Generators.Hom.toExtensionHom Λ A A _ _ _ (Generators.self Λ A)
      Λ B B _ _ _ (Generators.self Λ B) inferInstance φ.toRingHom.toAlgebra
      inferInstance inferInstance (IsScalarTower.of_algHom φ) generatorsMap
  let chain :=
    @Algebra.Extension.NaiveCotangent.RestrictScalars.map Λ Λ A B _ _ _ _
      inferInstance inferInstance inferInstance φ.toRingHom.toAlgebra
      inferInstance inferInstance (IsScalarTower.of_algHom φ)
      (Generators.self Λ A).toExtension (Generators.self Λ B).toExtension extensionMap
  DerivedCategory.Q.map (extendMap chain embeddingDownNat) ≫
    DerivedCategory.Q.map
      (ComplexShape.Embedding.mapAppIso embeddingDownNat
        (ModuleCat.restrictScalars φ.toRingHom)
        (Algebra.naiveCotangent Λ B)).inv ≫
    (ModuleCat.restrictScalars φ.toRingHom).mapDerivedCategoryFactors.inv.app
      ((Algebra.naiveCotangent Λ B).extend embeddingDownNat)

end Algebra.NaiveCotangent
