/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.StructureSheafSurjectivity

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.HigherDirectImage

/-- An open neighbourhood of the fibre `Yₛ` on which flatness, the fibre-dimension
bound, degree-one vanishing, and structure-sheaf surjectivity hold, with the last
three properties preserved by arbitrary base change. -/
structure ContractionNeighborhood.{u} {X Y S : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (s : S) where
  /-- The chosen open neighbourhood in `Y`. -/
  openSet : Y.Opens
  /-- Every point of the fibre of `q` over `s` belongs to the chosen open. -/
  containsFiber : ∀ yₛ : q.fiber s, q.fiberι s yₛ ∈ openSet
  /-- The inverse image of the chosen open is flat over `S`. -/
  flatOverBase : Flat ((f ⁻¹ᵁ openSet).ι ≫ p)
  /-- The fibres of the restriction of `f` have dimension at most one. -/
  fiberDimensionLEOne : ∀ y : openSet,
    topologicalKrullDim ((f ∣_ openSet).fiber y) ≤ (1 : WithBot ℕ∞)
  /-- The restriction of `R¹ f_* 𝒪_X` to the chosen open vanishes. -/
  degreeOneIsZero : IsZero
    ((RingedSpace.Hom.higherDirectImageModule f.toShHom
      (SheafOfModules.unit X.ringCatSheaf) 1).over openSet)
  /-- The structure-sheaf map for the restricted morphism is locally surjective. -/
  structureSheafMapIsLocallySurjective : Sheaf.IsLocallySurjective
    (RingedSpace.Hom.commRingSheafPushforwardMap (f ∣_ openSet).toShHom)
  /-- The fibre-dimension bound persists after every cartesian base change. -/
  baseChangeFiberDimensionLEOne :
    ∀ {X' Y' : Scheme.{u}}
      (g' : X' ⟶ (f ⁻¹ᵁ openSet).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ openSet),
      IsPullback g' f' (f ∣_ openSet) g →
        ∀ y' : Y', topologicalKrullDim (f'.fiber y') ≤ (1 : WithBot ℕ∞)
  /-- Degree-one higher-direct-image vanishing persists after every cartesian base change. -/
  baseChangeDegreeOneIsZero :
    ∀ {X' Y' : Scheme.{u}}
      (g' : X' ⟶ (f ⁻¹ᵁ openSet).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ openSet),
      IsPullback g' f' (f ∣_ openSet) g →
        IsZero (RingedSpace.Hom.higherDirectImageModule f'.toShHom
          (SheafOfModules.unit X'.ringCatSheaf) 1)
  /-- Structure-sheaf local surjectivity persists after every cartesian base change. -/
  baseChangeStructureSheafMapIsLocallySurjective :
    ∀ {X' Y' : Scheme.{u}}
      (g' : X' ⟶ (f ⁻¹ᵁ openSet).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ openSet),
      IsPullback g' f' (f ∣_ openSet) g → Sheaf.IsLocallySurjective
        (RingedSpace.Hom.commRingSheafPushforwardMap f'.toShHom)

universe u

variable {X Y S : Scheme.{u}}

namespace ContractionNeighborhood

/-- Construct a contraction neighbourhood from an explicit open and its direct and
base-change-stable properties. -/
def of (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (s : S) (V : Y.Opens)
    (containsFiber : ∀ yₛ : q.fiber s, q.fiberι s yₛ ∈ V)
    (flatOverBase : Flat ((f ⁻¹ᵁ V).ι ≫ p))
    (fiberDimensionLEOne : ∀ y : V,
      topologicalKrullDim ((f ∣_ V).fiber y) ≤ (1 : WithBot ℕ∞))
    (degreeOneIsZero : IsZero
      ((RingedSpace.Hom.higherDirectImageModule f.toShHom
        (SheafOfModules.unit X.ringCatSheaf) 1).over V))
    (structureSheafMapIsLocallySurjective : Sheaf.IsLocallySurjective
      (RingedSpace.Hom.commRingSheafPushforwardMap (f ∣_ V).toShHom))
    (baseChangeFiberDimensionLEOne :
      ∀ {X' Y' : Scheme.{u}}
        (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ V),
        IsPullback g' f' (f ∣_ V) g →
          ∀ y' : Y', topologicalKrullDim (f'.fiber y') ≤ (1 : WithBot ℕ∞))
    (baseChangeDegreeOneIsZero :
      ∀ {X' Y' : Scheme.{u}}
        (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ V),
        IsPullback g' f' (f ∣_ V) g →
          IsZero (RingedSpace.Hom.higherDirectImageModule f'.toShHom
            (SheafOfModules.unit X'.ringCatSheaf) 1))
    (baseChangeStructureSheafMapIsLocallySurjective :
      ∀ {X' Y' : Scheme.{u}}
        (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ V),
        IsPullback g' f' (f ∣_ V) g → Sheaf.IsLocallySurjective
          (RingedSpace.Hom.commRingSheafPushforwardMap f'.toShHom)) :
    ContractionNeighborhood p q f s where
  openSet := V
  containsFiber := containsFiber
  flatOverBase := flatOverBase
  fiberDimensionLEOne := fiberDimensionLEOne
  degreeOneIsZero := degreeOneIsZero
  structureSheafMapIsLocallySurjective := structureSheafMapIsLocallySurjective
  baseChangeFiberDimensionLEOne := baseChangeFiberDimensionLEOne
  baseChangeDegreeOneIsZero := baseChangeDegreeOneIsZero
  baseChangeStructureSheafMapIsLocallySurjective :=
    baseChangeStructureSheafMapIsLocallySurjective

end ContractionNeighborhood

/-- The special-fibre hypotheses for a proper morphism in a commutative triangle
give an open neighbourhood of `Yₛ` on which flatness, dimension at most one,
degree-one vanishing, and structure-sheaf surjectivity hold, with the latter
three properties preserved by arbitrary base change. -/
@[stacks 0E7J]
theorem exists_contractionNeighborhood
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (sq : CommSq f p q (𝟙 S)) (s : S)
    [LocallyOfFinitePresentation p]
    (hflat : ∀ xₛ : p.fiber s, p.flatAt (p.fiberι s xₛ)) [IsProper f]
    (hdim : ∀ yₛ : q.fiber s,
      topologicalKrullDim
        ((Scheme.Hom.fiberMap p f (𝟙 S) q sq s).fiber yₛ) ≤ (1 : WithBot ℕ∞))
    (hH1 : IsZero
      (RingedSpace.Hom.higherDirectImageModule
        (Scheme.Hom.fiberMap p f (𝟙 S) q sq s).toShHom
        (SheafOfModules.unit (p.fiber s).ringCatSheaf) 1))
    [Sheaf.IsLocallySurjective
      (RingedSpace.Hom.commRingSheafPushforwardMap
        (Scheme.Hom.fiberMap p f (𝟙 S) q sq s).toShHom)] :
    Nonempty (ContractionNeighborhood p q f s) := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
