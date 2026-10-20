module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Homology.Additive

/-!
# Perfect complexes on algebraic spaces

Perfectness of complexes of `𝒪_X`-modules and of objects of `D(𝒪_X)` on the small étale
ringed site of an algebraic space.

The generic ringed-site perfectness predicates require `UnivLE` between the site universe and
the ring universe, which fails for the small étale site of an algebraic space. Perfectness
below is the same local strictly perfect quasi-isomorphism condition, stated directly on
complexes of `𝒪_X`-modules and on `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CochainComplex

/-- A complex of `𝒪_X`-modules is perfect if every object of the small étale site has a
cover on which the restricted complex receives a map from a strictly perfect complex
inducing cohomology isomorphisms in every degree. -/
def IsPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  ∀ U : smallEtaleSite X, ∃ T : (smallEtaleTopology X).Cover U, ∀ I : T.Arrow,
    ∃ E' : _root_.CochainComplex
        (SheafOfModules.{u} ((structureSheaf X).over I.Y)) ℤ,
      SheafOfModules.CochainComplex.IsStrictlyPerfect E' ∧
        ∃ alpha :
            E' ⟶ ((SheafOfModules.Localization.restriction (structureSheaf X) I.Y).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj E,
          ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap alpha j)

/-- Perfectness of a complex of `𝒪_X`-modules unfolds to strictly perfect local models
inducing cohomology isomorphisms on a cover of every étale object. -/
theorem isPerfect_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : _root_.CochainComplex (Modules X) ℤ) :
    IsPerfect E ↔
      ∀ U : smallEtaleSite X, ∃ T : (smallEtaleTopology X).Cover U, ∀ I : T.Arrow,
        ∃ E' : _root_.CochainComplex
            (SheafOfModules.{u} ((structureSheaf X).over I.Y)) ℤ,
          SheafOfModules.CochainComplex.IsStrictlyPerfect E' ∧
            ∃ alpha :
                E' ⟶ ((SheafOfModules.Localization.restriction (structureSheaf X) I.Y).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj E,
              ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap alpha j) := sorry

end CochainComplex

namespace ModuleDerived

/-- An object of `D(𝒪_X)` is perfect when it is isomorphic to the image of a perfect
complex of `𝒪_X`-modules. -/
abbrev IsPerfect {S : Scheme.{u}} {X : AlgebraicSpace S} (P : ModuleDerived X) : Prop :=
  ∃ F : _root_.CochainComplex (Modules X) ℤ, ∃ _ : P ≅ DerivedCategory.Q.obj F,
    CochainComplex.IsPerfect F

/-- Perfectness of a derived `𝒪_X`-module is equivalent to the existence of a perfect
complex representative. -/
theorem isPerfect_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (P : ModuleDerived X) :
    IsPerfect P ↔
      ∃ F : _root_.CochainComplex (Modules X) ℤ, ∃ _ : P ≅ DerivedCategory.Q.obj F,
        CochainComplex.IsPerfect F := sorry

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace
