/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology presheaves and sheaves on a ringed space

The presheaf owner is inherited from the opens-ringed-site derived cohomology functor.  The sheaf
owner remains the underlying additive sheaf of the module-valued homology object, which keeps the
usual RingedSpace object model available to downstream statements.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

variable {X : RingedSpace.{u}}

/-- The degree-`q` additive cohomology presheaf of a derived `𝒪_X`-module. -/
@[stacks 0BKJ "objectwise cohomology presheaf on a ringed space"]
abbrev presheaf (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) :
    (Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  RingedSite.Hom.ModuleDerived.cohomologyPresheaf X.opensRingedSite K q

/-- The degree-`q` additive cohomology sheaf of a derived `𝒪_X`-module. -/
@[stacks 0BKJ "cohomology sheaf on a ringed space"]
abbrev sheaf (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) :
    X.carrier.Sheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf X).obj ((DerivedCategory.homologyFunctor X.Modules q).obj K)

/-- The module-valued iterated open cohomology object `H^p(U, H^q(K))`. -/
@[stacks 0BKJ "iterated open cohomology object"]
abbrev openCohomology (E : ModuleDerived X) (U : Opens X.carrier) (p : ℕ) (q : ℤ) :
    ModuleCat (sectionsRingOnOpen X U) :=
  moduleCohomologyAtOpen U ((DerivedCategory.homologyFunctor X.Modules q).obj E) p

/-- The sheaf associated to the degree-`q` cohomology presheaf is the degree-`q` cohomology sheaf.
The presheaf and sheaf owners are kept distinct because their equality is not definitional. -/
@[stacks 0BKJ "sheafification of the objectwise cohomology presheaf"]
theorem sheafification_isomorphic (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) :
    IsIsomorphic (sheaf X K q)
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (presheaf X K q)) := sorry

/-- Evaluation of the cohomology presheaf over an open is canonically the corresponding open
hypercohomology group. -/
@[stacks 0BKJ "cohomology presheaf evaluated on an open"]
theorem presheaf_obj_isomorphic_openHypercohomology
    (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) (U : Opens X.carrier) :
    IsIsomorphic ((presheaf X K q).obj (op U))
      (moduleOpenHypercohomology X U K q) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

namespace AlgebraicGeometry.RingedSpaceCohomology

/-- `𝓗'[q](X, K)` is the canonical degree-`q` additive cohomology presheaf. -/
scoped notation:max "𝓗'[" q "](" X ", " K ")" =>
  AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.presheaf X K q

/-- `𝓗[q](X, K)` is the degree-`q` additive cohomology sheaf. -/
scoped notation:max "𝓗[" q "](" X ", " K ")" =>
  AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.sheaf X K q

end AlgebraicGeometry.RingedSpaceCohomology

end
