module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Cohomology
import StacksCheckRecall

/-!
# Exercise 111.43.5

A finite locally free degree-2 morphism of integral schemes, with 2 invertible
on the target, splits the structure-sheaf unit map and therefore injects
structure-sheaf cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Exercise 111.43.5 (1): if `f : X ⟶ Y` is finite locally free of degree 2, `X` and `Y`
are integral schemes, and `2` is invertible in `Γ(Y, ⊤)`, then the `𝒪_Y`-module map
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom : 𝒪_Y ⟶ f_* 𝒪_X` has a
left inverse. -/
@[stacks 0DAN] #check
  (AlgebraicGeometry.Scheme.Hom.instIsSplitMono_unitToPushforwardObjUnit :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFreeOfRank f 2] [IsIntegral X] [IsIntegral Y]
    [Invertible (2 : Γ(Y, ⊤))],
    IsSplitMono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))

/- Exercise 111.43.5 (1): there is an `𝒪_Y`-module map `τ : f_* 𝒪_X ⟶ 𝒪_Y` retracting
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`. -/
@[stacks 0DAN] #check (AlgebraicGeometry.Scheme.Hom.exists_leftInverse_unitToPushforwardObjUnit :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFreeOfRank f 2] [IsIntegral X] [IsIntegral Y]
    [Invertible (2 : Γ(Y, ⊤))],
    ∃ τ : f.pushforwardStructureModule ⟶ SheafOfModules.unit Y.ringCatSheaf,
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ τ = 𝟙 _)

/- Exercise 111.43.5 (2): under the same hypotheses, `structureSheafCohomologyMap f n :
H^n(Y, 𝒪_Y) ⟶ H^n(X, 𝒪_X)` is injective for every `n`. The invertibility of `2` is
essential: there exist finite locally free degree-2 morphisms of integral schemes for
which the degree-1 map is not injective. -/
@[stacks 0DAN] #check
  (AlgebraicGeometry.Scheme.Hom.structureSheafCohomologyMap_injective :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFreeOfRank f 2] [IsIntegral X] [IsIntegral Y]
    [Invertible (2 : Γ(Y, ⊤))] (n : ℕ),
    Function.Injective (AlgebraicGeometry.Scheme.Hom.structureSheafCohomologyMap f n))
