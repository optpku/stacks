/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition

/-!
# Cohomology of epimorphic inverse systems in derived quasi-coherent modules

Degreewise epimorphic cohomology transitions identify the cohomology of a derived
inverse limit with the ordinary inverse limit of the cohomology sheaves. The latter
is a homotopy limit and is acyclic in positive degrees on affine étale objects.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The sequential inverse system of degree-`q` cohomology sheaves of a tower in
`DerivedQCoh X`. -/
abbrev cohomologySystem (Ksys : SequentialInverseSystem (DerivedQCoh X)) (q : ℤ) :
    SequentialInverseSystem (Modules X) :=
  Ksys ⋙ inclusion X ⋙ DerivedCategory.homologyFunctor (Modules X) q

/-- The cohomology transition maps of a `DerivedQCoh` tower are epimorphisms in every
degree. -/
def cohomologyTransitionEpi (Ksys : SequentialInverseSystem (DerivedQCoh X)) : Prop :=
  ∀ (q : ℤ) (n : ℕ),
    Epi (SequentialInverseSystem.transitionMap (cohomologySystem Ksys q) (Nat.le_succ n))

/-- For a sequential system in `DerivedQCoh X` with epimorphic cohomology transitions,
the cohomology sheaf of a derived limit is isomorphic to the inverse limit of the
cohomology sheaves. -/
theorem cohomologySheaf_iso_limit_of_epi
    (Ksys : SequentialInverseSystem (DerivedQCoh X)) (K : ModuleDerived X)
    (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
    (h_epi : cohomologyTransitionEpi Ksys) (q : ℤ) :
    IsIsomorphic ((DerivedCategory.homologyFunctor (Modules X) q).obj K)
      (limit (cohomologySystem Ksys q)) :=
  sorry

/-- For such a sequential system, the ordinary inverse limit of the degree-`q`
cohomology sheaves, placed in degree zero, is a homotopy limit of their
degree-zero tower. -/
theorem cohomologySheaf_limit_isOf_of_epi
    (Ksys : SequentialInverseSystem (DerivedQCoh X)) (K : ModuleDerived X)
    (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
    (h_epi : cohomologyTransitionEpi Ksys) (q : ℤ) :
    HomotopyLimit.IsOf
      (cohomologySystem Ksys q ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ))
      ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
        (limit (cohomologySystem Ksys q))) :=
  sorry

/-- For such a sequential system, the inverse limit of the degree-`q` cohomology
sheaves has vanishing positive cohomology on every affine object of `X_étale`. -/
theorem cohomologySheaf_limit_higherCohomology_isZero_of_epi
    (Ksys : SequentialInverseSystem (DerivedQCoh X)) (K : ModuleDerived X)
    (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
    (h_epi : cohomologyTransitionEpi Ksys) (q : ℤ)
    (U : smallEtaleSite X) [IsAffine U.left.left] (p : ℕ) (hp : 0 < p)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero
      (Sheaf.H'
        ((SheafOfModules.toSheaf (structureSheaf X)).obj
          (limit (cohomologySystem Ksys q)))
        p U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

end
