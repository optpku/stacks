/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension.Compatible

/-!
# Obstructions to maps of mixed-scalar module extensions

Endpoint maps between two extensions along a first-order thickening determine a Baer
difference. When their infinitesimal-map square commutes, this difference descends to an
extension over the source ringed space and gives an obstruction in degree-one `Ext`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace (Modules)
open CategoryTheory.Abelian (Ext)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ModuleExtension

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'}

section

variable [IsFirstOrderThickening i]

/-- The infinitesimal-map square of `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ` commutes. -/
def infinitesimalMap_comm (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) : Prop :=
  CommSq E.infinitesimalMap_restrict (tensorHom (𝟙 (idealModule i)) φ) ψ
    G.infinitesimalMap_restrict

/-- Commutativity of the infinitesimal-map square is equality of the two `𝒪_X`-linear composites
`ℐ ⊗ ℱ ⟶ ℒ`. -/
theorem infinitesimalMap_comm_iff (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    infinitesimalMap_comm E G φ ψ ↔
      E.infinitesimalMap_restrict ≫ ψ =
        tensorHom (𝟙 (idealModule i)) φ ≫ G.infinitesimalMap_restrict :=
  ⟨fun h => h.w, fun h => ⟨h⟩⟩

end

private theorem differenceShortComplex_zero (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    biprod.lift E.ι (-((i _*).map ψ ≫ G.ι)) ≫
      biprod.desc (E.π ≫ (i _*).map φ) G.π = 0 := sorry

/-- The complex with maps `(1, -ψ)` and `(φ, 1)` between the two middle modules. -/
def differenceShortComplex (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    ShortComplex X'.Modules :=
  ShortComplex.mk (biprod.lift E.ι (-((i _*).map ψ ≫ G.ι)))
    (biprod.desc (E.π ≫ (i _*).map φ) G.π) (by exact differenceShortComplex_zero E G φ ψ)

/-- The differentials of the difference complex are the specified biproduct maps. -/
theorem differenceShortComplex_spec (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (differenceShortComplex E G φ ψ).f = biprod.lift E.ι (-((i _*).map ψ ≫ G.ι)) ∧
      (differenceShortComplex E G φ ψ).g = biprod.desc (E.π ≫ (i _*).map φ) G.π :=
  ⟨rfl, rfl⟩

private theorem differenceInclusion_cycle (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (G.ι ≫ biprod.inr) ≫ (differenceShortComplex E G φ ψ).g = 0 := sorry

/-- The target kernel maps into the middle homology through the second summand's cycles. -/
def differenceInclusion (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (i _*).obj G.kernel ⟶ (differenceShortComplex E G φ ψ).homology :=
  (differenceShortComplex E G φ ψ).liftCycles (G.ι ≫ biprod.inr)
    (by exact differenceInclusion_cycle E G φ ψ) ≫ (differenceShortComplex E G φ ψ).homologyπ

private theorem differenceProjection_boundary (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (differenceShortComplex E G φ ψ).toCycles ≫
      ((differenceShortComplex E G φ ψ).iCycles ≫ biprod.fst ≫ E.π) = 0 := sorry

/-- Projection onto the first summand induces a map from middle homology to the source quotient. -/
def differenceProjection (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (differenceShortComplex E G φ ψ).homology ⟶ (i _*).obj E.cokernel :=
  (differenceShortComplex E G φ ψ).descHomology
    ((differenceShortComplex E G φ ψ).iCycles ≫ biprod.fst ≫ E.π)
    (by exact differenceProjection_boundary E G φ ψ)

private theorem differenceSequence_zero (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    differenceInclusion E G φ ψ ≫ differenceProjection E G φ ψ = 0 := sorry

/-- The sequence from the target kernel through difference homology to the source quotient. -/
def differenceSequence (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    ShortComplex X'.Modules :=
  ShortComplex.mk (differenceInclusion E G φ ψ) (differenceProjection E G φ ψ)
    (by exact differenceSequence_zero E G φ ψ)

/-- The difference homology sequence is short exact for any pair of endpoint maps. -/
theorem differenceSequence_shortExact (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (differenceSequence E G φ ψ).ShortExact := sorry

variable [IsFirstOrderThickening i]

private theorem mapObstructionSequence_zero (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    ((asIso ((pullbackPushforwardAdjunction i).counit.app G.kernel)).inv ≫
      (i ^*).map (differenceSequence E G φ ψ).f) ≫
      ((i ^*).map (differenceSequence E G φ ψ).g ≫
        (asIso ((pullbackPushforwardAdjunction i).counit.app E.cokernel)).hom) = 0 := sorry

/-- Pullback of the difference homology sequence, with endpoints identified by the counit. -/
def mapObstructionSequence (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    ShortComplex X.Modules :=
  ShortComplex.mk
    ((asIso ((pullbackPushforwardAdjunction i).counit.app G.kernel)).inv ≫
      (i ^*).map (differenceSequence E G φ ψ).f)
    ((i ^*).map (differenceSequence E G φ ψ).g ≫
      (asIso ((pullbackPushforwardAdjunction i).counit.app E.cokernel)).hom)
    (by exact mapObstructionSequence_zero E G φ ψ)

/-- The descended sequence has the pulled-back homology middle and counit-conjugated maps. -/
theorem mapObstructionSequence_spec (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (mapObstructionSequence E G φ ψ).X₂ =
      (i ^*).obj (differenceShortComplex E G φ ψ).homology ∧
    (mapObstructionSequence E G φ ψ).f =
      (asIso ((pullbackPushforwardAdjunction i).counit.app G.kernel)).inv ≫
        (i ^*).map (differenceSequence E G φ ψ).f ∧
    (mapObstructionSequence E G φ ψ).g =
      (i ^*).map (differenceSequence E G φ ψ).g ≫
        (asIso ((pullbackPushforwardAdjunction i).counit.app E.cokernel)).hom :=
  ⟨rfl, rfl, rfl⟩

/-- Commutativity of the infinitesimal square makes the descended homology sequence short exact. -/
theorem mapObstructionSequence_shortExact (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    (mapObstructionSequence E G φ ψ).ShortExact := sorry

variable [HasExt.{u} X.Modules]

/-- The obstruction class `o(φ, ψ) ∈ Ext¹_{𝒪_X}(ℱ, ℒ)` of a pair of endpoint maps whose
infinitesimal-map square commutes. -/
noncomputable def mapObstruction (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    Ext E.cokernel G.kernel 1 :=
  (mapObstructionSequence_shortExact E G φ ψ hcomm).extClass

/-- The degree-one obstruction of endpoint maps vanishes exactly when there is a middle
morphism commuting with both kernel inclusions and cokernel projections. -/
theorem mapObstruction_eq_zero_iff (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    mapObstruction E G φ ψ hcomm = 0 ↔
      ∃ φ' : E.middle ⟶ G.middle,
        E.ι ≫ φ' = (i _*).map ψ ≫ G.ι ∧
          φ' ≫ G.π = E.π ≫ (i _*).map φ := sorry

end AlgebraicGeometry.RingedSpace.Hom.ModuleExtension
