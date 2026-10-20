/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Cohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.StructureSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- Derived pullback of `K` along the structural morphism of a scheme over `B`. -/
abbrev pullbackOver (K : ModuleDerived B) (σ : SchemeOver B) :
    ModuleDerived (ofOver σ.left) :=
  (pullback σ.hom).obj K

/-- `pullbackOver K σ` is unbounded derived pullback of `K` along `σ.hom`. -/
theorem pullbackOver_eq (K : ModuleDerived B) (σ : SchemeOver B) :
    pullbackOver K σ = (pullback σ.hom).obj K :=
  rfl

/-- Restriction of `H^0(Lg^* K)`-sections along a morphism of schemes over `B`. -/
def cohomologyZeroRestrict (K : ModuleDerived B) {σ τ : SchemeOver B} (h : τ ⟶ σ)
    (ψ : SheafOfModules.unit (structureSheaf (ofOver σ.left)) ⟶
      cohomologySheaf (pullbackOver K σ) 0) :
    SheafOfModules.unit (structureSheaf (ofOver τ.left)) ⟶
      cohomologySheaf (pullbackOver K τ) 0 :=
  structureModulePullbackInv ((ofOverFunctor S).map h.left) ≫
    (Modules.pullback ((ofOverFunctor S).map h.left)).map ψ ≫
      cohomologySheafPullbackComparison ((ofOverFunctor S).map h.left)
          (pullbackOver K σ) 0 ≫
        (DerivedCategory.homologyFunctor (Modules (ofOver τ.left)) 0).map
          ((pullbackCompComparison ((ofOverFunctor S).map h.left) σ.hom).app K) ≫
          eqToHom
            (congrArg (fun k ↦ cohomologySheaf ((pullback k).obj K) 0)
              (CostructuredArrow.w h))

/-- Restriction of derived Hom-sections `Hom(𝒪_T[0], Lg^* K)` along a morphism of
schemes over `B`. -/
def derivedZeroRestrict (K : ModuleDerived B) {σ τ : SchemeOver B} (h : τ ⟶ σ)
    (u : structureSheafDerived (ofOver σ.left) ⟶ pullbackOver K σ) :
    structureSheafDerived (ofOver τ.left) ⟶ pullbackOver K τ :=
  structureSheafDerivedPullbackUnit ((ofOverFunctor S).map h.left) ≫
    (pullback ((ofOverFunctor S).map h.left)).map u ≫
      (pullbackCompComparison ((ofOverFunctor S).map h.left) σ.hom).app K ≫
        eqToHom (congrArg (fun k ↦ (pullback k).obj K) (CostructuredArrow.w h))

/-- Restriction of degree-zero cohomology sections along the identity is the identity. -/
theorem cohomologyZeroRestrict_id (K : ModuleDerived B) (σ : SchemeOver B) :
    cohomologyZeroRestrict K (𝟙 σ) = id := sorry

/-- Restriction of degree-zero cohomology sections is contravariantly compatible with composition.
-/
theorem cohomologyZeroRestrict_comp (K : ModuleDerived B) {σ τ υ : SchemeOver B}
    (h : τ ⟶ σ) (k : υ ⟶ τ) :
    cohomologyZeroRestrict K (k ≫ h) = cohomologyZeroRestrict K k ∘ cohomologyZeroRestrict K h := sorry

/-- The functor `T ↦ H^0(T, H^0(Lg^* K))` on schemes over `B`. -/
def cohomologyZeroFunctor (K : ModuleDerived B) :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ :=
    SheafOfModules.unit (structureSheaf (ofOver σ.unop.left)) ⟶
      cohomologySheaf (pullbackOver K σ.unop) 0
  map h := TypeCat.ofHom (cohomologyZeroRestrict K h.unop)
  map_id σ := congrArg TypeCat.ofHom (cohomologyZeroRestrict_id K σ.unop)
  map_comp h k := congrArg TypeCat.ofHom (cohomologyZeroRestrict_comp K h.unop k.unop)

/-- Evaluating `cohomologyZeroFunctor K` at a scheme over `B` yields Hom from the
structure sheaf into the degree-zero cohomology sheaf of derived pullback. -/
theorem cohomologyZeroFunctor_obj (K : ModuleDerived B) (σ : SchemeOver B) :
    (cohomologyZeroFunctor K).obj (op σ) =
      (SheafOfModules.unit (structureSheaf (ofOver σ.left)) ⟶
        cohomologySheaf (pullbackOver K σ) 0) :=
  rfl

/-- `cohomologyZeroFunctor` acts on morphisms of schemes over `B` by
`cohomologyZeroRestrict`. -/
theorem cohomologyZeroFunctor_map (K : ModuleDerived B) {σ τ : SchemeOver B}
    (h : τ ⟶ σ) :
    (cohomologyZeroFunctor K).map h.op = TypeCat.ofHom (cohomologyZeroRestrict K h) :=
  rfl

/-- Restriction of derived degree-zero sections along the identity is the identity. -/
theorem derivedZeroRestrict_id (K : ModuleDerived B) (σ : SchemeOver B) :
    derivedZeroRestrict K (𝟙 σ) = id := sorry

/-- Restriction of derived degree-zero sections is contravariantly compatible with composition. -/
theorem derivedZeroRestrict_comp (K : ModuleDerived B) {σ τ υ : SchemeOver B}
    (h : τ ⟶ σ) (k : υ ⟶ τ) :
    derivedZeroRestrict K (k ≫ h) = derivedZeroRestrict K k ∘ derivedZeroRestrict K h := sorry

/-- The functor `T ↦ H^0(T, Lg^* K)` on schemes over `B`. -/
def derivedZeroFunctor (K : ModuleDerived B) :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := structureSheafDerived (ofOver σ.unop.left) ⟶ pullbackOver K σ.unop
  map h := TypeCat.ofHom (derivedZeroRestrict K h.unop)
  map_id σ := congrArg TypeCat.ofHom (derivedZeroRestrict_id K σ.unop)
  map_comp h k := congrArg TypeCat.ofHom (derivedZeroRestrict_comp K h.unop k.unop)

/-- Evaluating `derivedZeroFunctor K` at a scheme over `B` yields derived Hom from
`𝒪_T[0]` into `Lg^* K`. -/
theorem derivedZeroFunctor_obj (K : ModuleDerived B) (σ : SchemeOver B) :
    (derivedZeroFunctor K).obj (op σ) =
      (structureSheafDerived (ofOver σ.left) ⟶ pullbackOver K σ) :=
  rfl

/-- `derivedZeroFunctor` acts on morphisms of schemes over `B` by
`derivedZeroRestrict`. -/
theorem derivedZeroFunctor_map (K : ModuleDerived B) {σ τ : SchemeOver B}
    (h : τ ⟶ σ) :
    (derivedZeroFunctor K).map h.op = TypeCat.ofHom (derivedZeroRestrict K h) :=
  rfl

/-- Under vanishing of all negative cohomology of derived pullbacks, derived Hom from
`𝒪_T[0]` agrees with global sections of `H^0(Lg^* K)`. -/
theorem derivedZeroFunctorIso_of_negativeVanishing (K : ModuleDerived B)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)) :
    Nonempty (derivedZeroFunctor K ≅ cohomologyZeroFunctor K) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
