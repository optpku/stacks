module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Structure-sheaf splitting and cohomology of finite locally free morphisms

A finite locally free degree-two morphism between integral schemes splits the
structure-sheaf unit and induces injective cohomology maps when two is invertible
on the target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a finite locally free degree-two morphism between integral schemes, with
two invertible on the target, the structure-sheaf unit is a split monomorphism. -/
@[stacks 0DAN]
instance instIsSplitMono_unitToPushforwardObjUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFreeOfRank f 2] [IsIntegral X] [IsIntegral Y]
    [Invertible (2 : Γ(Y, ⊤))] :
    IsSplitMono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := sorry

/-- For a finite locally free degree-two morphism between integral schemes, with
two invertible on the target, there is an `𝒪_Y`-module map
`τ : f_* 𝒪_X ⟶ 𝒪_Y` retracting the structure-sheaf unit. -/
theorem exists_leftInverse_unitToPushforwardObjUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFreeOfRank f 2] [IsIntegral X] [IsIntegral Y]
    [Invertible (2 : Γ(Y, ⊤))] :
    ∃ τ : f.pushforwardStructureModule ⟶ SheafOfModules.unit Y.ringCatSheaf,
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ τ = 𝟙 _ := sorry

/-- A finite locally free degree-two morphism between integral schemes, with two
invertible on the target, induces an injective structure-sheaf cohomology map in
every nonnegative degree. -/
@[stacks 0DAN]
theorem structureSheafCohomologyMap_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFreeOfRank f 2] [IsIntegral X] [IsIntegral Y]
    [Invertible (2 : Γ(Y, ⊤))] (n : ℕ) :
    Function.Injective (structureSheafCohomologyMap f n) := sorry

end AlgebraicGeometry.Scheme.Hom
