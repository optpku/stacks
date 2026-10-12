/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory ExactFunctor.Derived.Bounded

universe u w

namespace AlgebraicGeometry.Scheme.DerivedCoh

/-- Bounded derived restriction of coherent modules along an open immersion into a
Noetherian scheme is essentially surjective. -/
instance restrictEssSurj {X U : Scheme.{u}} (j : U ⟶ X)
    [IsNoetherian X] [IsOpenImmersion j]
    [HasDerivedCategory.{w} (RingedSpace.Coh X.toRingedSpace)]
    [HasDerivedCategory.{w} (RingedSpace.Coh U.toRingedSpace)] :
    (functor (ExactFunctor.of (Modules.coherentRestrictFunctor j))).EssSurj := sorry

end AlgebraicGeometry.Scheme.DerivedCoh
