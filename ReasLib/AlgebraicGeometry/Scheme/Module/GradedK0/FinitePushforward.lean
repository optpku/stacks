module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FinitePushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedK0.Equivalence
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Functor

/-!
# Finite pushforward on filtered and graded Grothendieck groups

This file defines the homomorphisms induced by finite pushforward on filtered
and dimension-graded Grothendieck groups and their comparison with cycle pushforward.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.FinitePushforward

variable {S : Scheme.{u}} {X Y : Over S} (π : X ⟶ Y)
  [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsFinite π.left]
  (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]

/-- The homomorphism on filtered coherent `K₀` induced by finite pushforward. -/
noncomputable def k0 (k : ℤ) :
    AbelianK0
        (RingedSpace.CohLE X.left.toRingedSpace (X.hom.relativeDimensionFunction δ) k) →+
      AbelianK0
        (RingedSpace.CohLE Y.left.toRingedSpace (Y.hom.relativeDimensionFunction δ) k) :=
  AbelianK0.map (cohLEExact π δ k)

/-- Filtered finite pushforward sends an object class to the class of its pushforward. -/
theorem k0_of (k : ℤ)
    (F : RingedSpace.CohLE X.left.toRingedSpace
      (X.hom.relativeDimensionFunction δ) k) :
    k0 π δ k (AbelianK0.of F) = AbelianK0.of ((cohLE π δ k).obj F) := sorry

/-- Finite pushforward on the dimension-graded coherent `K₀`, defined through the canonical
cycle comparison maps. -/
noncomputable def gradedK0 (k : ℤ) :
    Scheme.Modules.GradedK0 X.hom δ k →+ Scheme.Modules.GradedK0 Y.hom δ k :=
  (Scheme.Modules.GradedK0.toK0 Y.hom δ k).comp
    ((CycleGroup.mapHom π.left (X.hom.relativeDimensionFunction δ)
      (Y.hom.relativeDimensionFunction δ) k).comp
        (Scheme.Modules.GradedK0.toCycle X.hom δ k))

/-- Graded finite pushforward sends the quotient class of a filtered coherent sheaf to the
quotient class of its finite pushforward. -/
theorem gradedK0_of (k : ℤ)
    (F : RingedSpace.CohLE X.left.toRingedSpace
      (X.hom.relativeDimensionFunction δ) k) :
    gradedK0 π δ k (Scheme.Modules.GradedK0.of X.hom δ k F) =
      Scheme.Modules.GradedK0.of Y.hom δ k ((cohLE π δ k).obj F) := sorry

/-- The cycle-to-graded-`K₀` comparison commutes with finite pushforward. -/
theorem toK0_naturality (k : ℤ) :
    (gradedK0 π δ k).comp (Scheme.Modules.GradedK0.toK0 X.hom δ k) =
      (Scheme.Modules.GradedK0.toK0 Y.hom δ k).comp
        (CycleGroup.mapHom π.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) k) := sorry

/-- The graded-`K₀`-to-cycle comparison commutes with finite pushforward. -/
theorem toCycle_naturality (k : ℤ) :
    (CycleGroup.mapHom π.left (X.hom.relativeDimensionFunction δ)
      (Y.hom.relativeDimensionFunction δ) k).comp
        (Scheme.Modules.GradedK0.toCycle X.hom δ k) =
      (Scheme.Modules.GradedK0.toCycle Y.hom δ k).comp (gradedK0 π δ k) := sorry

end AlgebraicGeometry.Scheme.Modules.FinitePushforward
