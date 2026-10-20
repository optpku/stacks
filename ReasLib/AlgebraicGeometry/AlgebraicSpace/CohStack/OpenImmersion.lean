/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiCompact.Cancellation

/-!
# Open immersions of coherent-sheaf stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Fibrewise pushforward along an open immersion between algebraic spaces
separated and of finite presentation over `B` defines a morphism of their
coherent-sheaf groupoid fibrations. -/
def mapOfOpenImmersion (π : X ⟶ Y) (y : Y ⟶ B) [IsOpenImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    toGroupoids (π ≫ y) ⟶ toGroupoids y :=
  @map S X Y B π y
    { toFiniteType :=
        { toQuasiCompact := QuasiCompact.of_comp π y
          toLocallyOfFiniteType := inferInstance }
      locallyQuasiFinite := inferInstance }
    inferInstance inferInstance inferInstance inferInstance

/-- Pushforward specialized to an open immersion agrees with the quasi-finite
pushforward whenever quasi-finiteness is supplied independently. -/
theorem mapOfOpenImmersion_eq_map (π : X ⟶ Y) (y : Y ⟶ B)
    [IsOpenImmersion π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    mapOfOpenImmersion π y = map π y := sorry

/-- Fibrewise pushforward along an open immersion between algebraic spaces
separated and of finite presentation over `B` is an open immersion of
coherent-sheaf groupoid fibrations. -/
instance instOpenImmersion_map (π : X ⟶ Y) (y : Y ⟶ B) [IsOpenImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    OpenImmersion (mapOfOpenImmersion π y) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
