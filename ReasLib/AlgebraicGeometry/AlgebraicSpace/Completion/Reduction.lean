module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Completion
public import ReasLib.AlgebraicGeometry.Presheaf.Reduction

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Completion

variable {S : Scheme.{u}} {X Z : (Over S)ᵒᵖ ⥤ Type u}

/-- The reduction of a closed subspace maps into its ambient completion. -/
theorem range_reduction_le (inclusion : Z ⟶ X) (hX : IsAlgebraicSpace X)
    (hZ : IsAlgebraicSpace Z)
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion) :
    Subfunctor.range ((SpacePresheaf.reduction Z).ι ≫ inclusion) ≤ subfunctor inclusion := sorry

/-- The canonical morphism from the reduction of a closed subspace to the
completion along that subspace. -/
noncomputable def fromReduction (inclusion : Z ⟶ X) (hX : IsAlgebraicSpace X)
    (hZ : IsAlgebraicSpace Z)
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion) :
    (SpacePresheaf.reduction Z).toFunctor ⟶ (subfunctor inclusion).toFunctor :=
  Subfunctor.lift ((SpacePresheaf.reduction Z).ι ≫ inclusion)
    (range_reduction_le inclusion hX hZ hClosed)

/-- The canonical morphism from the reduced subspace to the completion
commutes with the inclusions into the ambient presheaf. -/
theorem fromReduction_comp_ι (inclusion : Z ⟶ X) (hX : IsAlgebraicSpace X)
    (hZ : IsAlgebraicSpace Z)
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion) :
    fromReduction inclusion hX hZ hClosed ≫ (subfunctor inclusion).ι =
      (SpacePresheaf.reduction Z).ι ≫ inclusion := sorry

/-- The reduction of the completion along a closed subspace equals the
reduction of that subspace as an embedded subfunctor of the ambient space. -/
theorem reduction_eq (inclusion : Z ⟶ X) (hX : IsAlgebraicSpace X)
    (hZ : IsAlgebraicSpace Z)
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion) :
    (SpacePresheaf.reduction (subfunctor inclusion).toFunctor).image (subfunctor inclusion).ι =
      (SpacePresheaf.reduction Z).image inclusion := sorry

/-- The reduced subsheaf of the completion along a closed algebraic subspace
is an algebraic space. -/
theorem reduction_isAlgebraicSpace (inclusion : Z ⟶ X) (hX : IsAlgebraicSpace X)
    (hZ : IsAlgebraicSpace Z)
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion) :
    IsAlgebraicSpace (SpacePresheaf.reduction (subfunctor inclusion).toFunctor).toFunctor := sorry

/-- The reduced subsheaf of the completion along a closed algebraic subspace
admits a reduced étale atlas. -/
theorem reduction_hasReducedEtaleAtlas (inclusion : Z ⟶ X) (hX : IsAlgebraicSpace X)
    (hZ : IsAlgebraicSpace Z)
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion) :
    SpacePresheaf.HasReducedEtaleAtlas
      (SpacePresheaf.reduction (subfunctor inclusion).toFunctor).toFunctor := sorry

/-- The inclusion of the reduced subsheaf into the completion along a closed
algebraic subspace is a representable surjective closed immersion. -/
theorem reductionι_isThickening (inclusion : Z ⟶ X) (hX : IsAlgebraicSpace X)
    (hZ : IsAlgebraicSpace Z)
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion) :
    Scheme.representableMorphismProperty S (@IsClosedImmersion ⊓ @Surjective)
      (SpacePresheaf.reduction (subfunctor inclusion).toFunctor).ι := sorry

end AlgebraicGeometry.AlgebraicSpace.Completion
