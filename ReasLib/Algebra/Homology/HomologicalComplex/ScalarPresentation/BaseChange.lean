/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.Algebra.Homology.HomologicalComplex.ScalarPresentation
public import ReasLib.RingTheory.FittingIdeal.BaseChange

/-!
# Base change of scalar presentations

The determinantal ideal attached to a scalar and a differential commutes with extension of
scalars.  The statement is independent of a chain/cochain convention and uses the canonical
prolongation of `ModuleCat.extendScalars` to homological complexes.
@stack 0GSU
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u s m w

namespace HomologicalComplex.ScalarPresentation

variable {R : Type u} [CommRing R]
variable {ι : Type w} {c : ComplexShape ι}

/-- Degreewise form of `ModuleCat.ExtendScalars.finite`, exposed so typeclass search can see through a
homological-complex evaluation. -/
@[stacks 08JZ "scalar-extension finite complex terms"]
instance extendScalars_complex_finite
    {S : Type s} [CommRing S] [Algebra R S]
    (K : HomologicalComplex (ModuleCat.{m} R) c) (i : ι)
    [Module.Finite R (K.X i)] :
    Module.Finite S
      ((((ModuleCat.extendScalars.{u, s, m} (algebraMap R S)).mapHomologicalComplex c).obj K).X i) :=
  sorry

/-- Degreewise form of `ModuleCat.ExtendScalars.free`, exposed for mapped homological complexes. -/
@[stacks 08JZ "scalar-extension free complex terms"]
instance extendScalars_complex_free
    {S : Type s} [CommRing S] [Algebra R S]
    (K : HomologicalComplex (ModuleCat.{m} R) c) (i : ι)
    [Module.Free R (K.X i)] :
    Module.Free S
      ((((ModuleCat.extendScalars.{u, s, m} (algebraMap R S)).mapHomologicalComplex c).obj K).X i) :=
  sorry

/-- Scalar-presentation determinantal ideals commute with extension of scalars.  No regularity
assumption on the scalar and no freeness assumption on the presentation source are needed. -/
@[stacks 0GSU "base change of scalar-presentation determinantal ideals"]
theorem fittingIdeal_baseChange
    {S : Type s} [CommRing S] [Algebra R S]
    (f : R) (K : HomologicalComplex (ModuleCat.{m} R) c) (i j : ι)
    [Module.Finite R (K.X i)]
    [Module.Free R (K.X j)] [Module.Finite R (K.X j)] :
    fittingIdeal (algebraMap R S f)
        (((ModuleCat.extendScalars.{u, s, m} (algebraMap R S)).mapHomologicalComplex c).obj K)
          i j =
      Ideal.map (algebraMap R S) (fittingIdeal f K i j) := sorry

end HomologicalComplex.ScalarPresentation
