/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Linear
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A proper-smooth pair of schemes over a field equipped with a linear, exact, fully faithful
functor between their perfect derived categories. -/
structure ProperSmoothPerfectEmbedding (k : Type u) [Field k] where
  /-- The source scheme over `k`. -/
  X : SchemeOverField k
  /-- The target scheme over `k`. -/
  Y : SchemeOverField k
  /-- Properness of the source structural morphism. -/
  proper_X : IsProper X.hom
  /-- Smoothness of the source structural morphism. -/
  smooth_X : Smooth X.hom
  /-- Properness of the target structural morphism. -/
  proper_Y : IsProper Y.hom
  /-- Smoothness of the target structural morphism. -/
  smooth_Y : Smooth Y.hom
  /-- The functor between the perfect derived categories. -/
  F : RingedSpace.ModuleDerived.Perfect (X := X.left.toRingedSpace) ⥤
    RingedSpace.ModuleDerived.Perfect (X := Y.left.toRingedSpace)
  /-- Linearity of the functor for the structural scalar actions. -/
  linear : Scheme.ModuleDerived.Perfect.IsLinearFor X.hom Y.hom F
  /-- Exactness of the functor. -/
  exact : F.HasTriangulatedStructure
  /-- Surjectivity of the functor on every morphism set. -/
  full : F.Full
  /-- Injectivity of the functor on every morphism set. -/
  faithful : F.Faithful

/-- Construct a proper-smooth perfect embedding from its schemes, certificates, and functorial
properties. -/
def ProperSmoothPerfectEmbedding.of
    (k : Type u) [Field k]
    (X Y : SchemeOverField k)
    (proper_X : IsProper X.hom) (smooth_X : Smooth X.hom)
    (proper_Y : IsProper Y.hom) (smooth_Y : Smooth Y.hom)
    (F : RingedSpace.ModuleDerived.Perfect (X := X.left.toRingedSpace) ⥤
      RingedSpace.ModuleDerived.Perfect (X := Y.left.toRingedSpace))
    (linear : Scheme.ModuleDerived.Perfect.IsLinearFor X.hom Y.hom F)
    (exact : F.HasTriangulatedStructure) (full : F.Full) (faithful : F.Faithful) :
    ProperSmoothPerfectEmbedding k :=
  { X := X
    Y := Y
    proper_X := proper_X
    smooth_X := smooth_X
    proper_Y := proper_Y
    smooth_Y := smooth_Y
    F := F
    linear := linear
    exact := exact
    full := full
    faithful := faithful }

variable {k : Type u} [Field k]

/-- The source scheme in a proper-smooth perfect embedding is proper and smooth over the field. -/
theorem ProperSmoothPerfectEmbedding.source_spec
    (E : ProperSmoothPerfectEmbedding k) :
    IsProper E.X.hom ∧ Smooth E.X.hom := sorry

/-- The target scheme in a proper-smooth perfect embedding is proper and smooth over the field. -/
theorem ProperSmoothPerfectEmbedding.target_spec
    (E : ProperSmoothPerfectEmbedding k) :
    IsProper E.Y.hom ∧ Smooth E.Y.hom := sorry

/-- The functor in a proper-smooth perfect embedding is linear for the structural actions and
exact. -/
theorem ProperSmoothPerfectEmbedding.linear_exact
    (E : ProperSmoothPerfectEmbedding k) :
    Scheme.ModuleDerived.Perfect.IsLinearFor E.X.hom E.Y.hom E.F ∧
      E.F.HasTriangulatedStructure := sorry

/-- The functor in a proper-smooth perfect embedding induces bijections on all morphism sets. -/
theorem ProperSmoothPerfectEmbedding.map_bijective
    (E : ProperSmoothPerfectEmbedding k) (A B :
      RingedSpace.ModuleDerived.Perfect (X := E.X.left.toRingedSpace)) :
    Function.Bijective (E.F.map : (A ⟶ B) → (E.F.obj A ⟶ E.F.obj B)) := sorry

end AlgebraicGeometry.SchemeOverField
