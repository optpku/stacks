module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Below Injective Derived Comparison

The canonical comparison from the bounded-below homotopy category of injective
complexes to the bounded-below derived category is fully faithful and preserves
distinguished triangles. It is an equivalence when the abelian category has
enough injectives.
-/

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.HomotopyCategory.Plus.Injective

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical functor from bounded-below injective homotopy
objects to the bounded-below derived category. -/
@[stacks 013V]
def toDerived : HomotopyCategory.Plus.Injective 𝒜 ⥤ DerivedCategory.Plus 𝒜 :=
  HomotopyCategory.Plus.Injective.ι 𝒜 ⋙ DerivedCategory.Plus.Qh

namespace toDerived

/-- The canonical comparison from bounded-below injective homotopy objects commutes
with shifts through the shift comparisons of the inclusion and localization. -/
instance commShift : (Injective.toDerived 𝒜).CommShift ℤ :=
  Functor.CommShift.comp (Injective.ι 𝒜) DerivedCategory.Plus.Qh

/-- The canonical comparison from bounded-below injective homotopy objects to the
bounded-below derived category preserves distinguished triangles. -/
instance isTriangulated : (Injective.toDerived 𝒜).IsTriangulated := sorry

/-- Morphisms between bounded-below injective homotopy objects are detected
bijectively after passage to the bounded-below derived category. -/
@[stacks 013V]
theorem map_bijective (X Y : HomotopyCategory.Plus.Injective 𝒜) :
    Function.Bijective ((Injective.toDerived 𝒜).map : (X ⟶ Y) → _) := sorry

/-- The canonical functor from bounded-below injective homotopy objects is full. -/
@[stacks 013V]
instance full : (Injective.toDerived 𝒜).Full := sorry

/-- The canonical functor from bounded-below injective homotopy objects is faithful. -/
@[stacks 013V]
instance faithful : (Injective.toDerived 𝒜).Faithful := sorry

variable {𝒜}

/-- If an abelian category has enough injectives, bounded-below injective homotopy
objects compute its bounded-below derived category. -/
@[stacks 013V]
instance isEquivalence [EnoughInjectives 𝒜] :
    Functor.IsEquivalence (Injective.toDerived 𝒜) := sorry

end toDerived

end CategoryTheory.HomotopyCategory.Plus.Injective
