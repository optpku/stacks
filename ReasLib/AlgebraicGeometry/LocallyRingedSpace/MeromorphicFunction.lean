/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Meromorphic functions on a locally ringed space

The sheaf of meromorphic functions is the sheafification of the total-quotient presheaf of the
structure sheaf. This file also exposes the canonical maps from regular functions to meromorphic
functions on stalks, opens, and global sections.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The presheaf of sections whose germ at every point is a non-zero-divisor in the
corresponding stalk. -/
noncomputable abbrev meromorphicFunctionDenominators :
    TopCat.Presheaf.SubmonoidPresheaf X.presheaf :=
  X.presheaf.submonoidPresheafOfStalk fun x ↦
    nonZeroDivisors (X.presheaf.stalk x)

/-- A section belongs to the meromorphic-function denominator presheaf exactly when all of its
germs are non-zero-divisors. -/
theorem mem_meromorphicFunctionDenominators_iff
    {U : Opens X} (s : X.presheaf.obj (op U)) :
    s ∈ (meromorphicFunctionDenominators X).obj (op U) ↔
      ∀ x : U, X.presheaf.germ U x.1 x.2 s ∈
        nonZeroDivisors (X.presheaf.stalk x.1) := sorry

/-- The sheaf of meromorphic functions on a locally ringed space is the sheaf associated to the
total-quotient presheaf of its structure sheaf. -/
@[stacks 01X2 "meromorphic function sheaf"]
abbrev meromorphicFunctionSheaf : TopCat.Sheaf CommRingCat X.toTopCat :=
  (presheafToSheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat).obj
    (TopCat.Presheaf.totalQuotientPresheaf X.𝒪.presheaf)

/-- The canonical morphism from the structure sheaf to the sheaf of meromorphic functions. -/
@[stacks 01X2 "structure-sheaf map"]
noncomputable abbrev toMeromorphicFunctionSheafHom :
  X.𝒪 ⟶ meromorphicFunctionSheaf X :=
  (sheafificationIso X.𝒪).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat).map
      (TopCat.Presheaf.toTotalQuotientPresheaf X.𝒪.presheaf)

/-- The canonical algebra map from the stalk `𝒪_{X,x}` to the meromorphic stalk `𝒦_{X,x}`. -/
noncomputable instance instAlgebraStalkMeromorphicFunctionSheaf (x : X) :
    Algebra (X.presheaf.stalk x) ((meromorphicFunctionSheaf X).presheaf.stalk x) :=
  RingHom.toAlgebra
    (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (toMeromorphicFunctionSheafHom X).hom).hom)

/-- The canonical algebra map from regular sections on `U` to meromorphic sections on `U`. -/
noncomputable instance instAlgebraSectionsMeromorphicFunctionSheaf (U : Opens X.toTopCat) :
    Algebra (X.presheaf.obj (op U)) ((meromorphicFunctionSheaf X).presheaf.obj (op U)) :=
  RingHom.toAlgebra
    (((toMeromorphicFunctionSheafHom X).hom.app (op U)).hom)

/-- The meromorphic functions on `X` are the global sections of its meromorphic function sheaf. -/
@[stacks 01X2 "meromorphic functions"]
abbrev meromorphicFunctions : CommRingCat :=
  (meromorphicFunctionSheaf X).presheaf.obj (op ⊤)

/-- The canonical map from regular global sections to meromorphic functions. -/
noncomputable abbrev toMeromorphicFunctions :
    X.presheaf.obj (op ⊤) ⟶ meromorphicFunctions X :=
  (toMeromorphicFunctionSheafHom X).hom.app (op ⊤)

end AlgebraicGeometry.LocallyRingedSpace
