/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Cohomology
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise

/-!
# Cohomology of module presheaves on standard big sites

The reusable constructions and comparison for standard-site cohomology are
provided by their mathematical library owners.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- The functorial standard-site cohomology construction. -/
#check (PresheafOfModules.standardCohomologyFunctor :
  ∀ (S : Scheme.{u}) (τ : StandardTopology) (U : Over S) (p : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
    PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf) ⥤
      AddCommGrpCat.{u})

/- The degree-`p` cohomology object of an associated additive sheaf. -/
#check (PresheafOfModules.standardCohomology :
  ∀ {S : Scheme.{u}}
    (ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf))
    (τ : StandardTopology) (U : Over S) (p : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
    AddCommGrpCat.{u})

/- The concrete geometric interpretation of each standard precoverage's
morphism property. -/
#check (AlgebraicGeometry.StandardTopology.morphismProperty_iff :
  ∀ (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y),
    τ.precoverage.morphismProperty f ↔
      match τ with
      | .zariski => IsOpenImmersion f
      | .etale => Etale f
      | .smooth => Smooth f
      | .syntomic => Syntomic f
      | .fppf => Flat f ∧ LocallyOfFinitePresentation f)
