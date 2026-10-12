/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Norm.Defs
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_47_3_RationalFunction
public import stacks_project.Chap72.Definition_72_4_1_Integral
import stacks_project.Chap72.Lemma_72_4_2_Comparison
import stacks_project.Chap72.Lemma_72_5_1
import stacks_project.Chap76.Lemma_76_36_2_PointsOver

/-!
# Function-field norms of morphisms of integral algebraic spaces

A dominant morphism of integral algebraic spaces induces a ring homomorphism
on rational function fields by transporting the residue-field homomorphism at
a generic point across `rationalFunctionRingEquivResidueField`. The associated
algebra is morphism-local, and the field norm on units is `Nm_{R(X)/R(Y)}`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The homomorphism `R(Y) →+* R(X)` induced by a dominant morphism of integral
algebraic spaces, obtained by transporting `residueFieldMap` at a generic point
across `rationalFunctionRingEquivResidueField`. -/
public noncomputable def rationalFunctionMap {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [Dominant p] : RationalFunction Y →+* RationalFunction X :=
  let hη := exists_mem_genericPoints (X := X)
  let η := hη.choose
  let eX := rationalFunctionRingEquivResidueField hη.choose_spec
  let eY := rationalFunctionRingEquivResidueField
    (map_mem_genericPoints_of_isDominant p hη.choose_spec)
  eX.symm.toRingHom.comp
    ((RingHom.ulift.{u + 1, u + 1} (residueFieldMap p η).hom).comp eY.toRingHom)

/-- The morphism-local algebra structure on `R(X)` over `R(Y)` induced by a
dominant morphism of integral algebraic spaces. -/
@[expose, reducible]
public noncomputable def rationalFunctionAlgebra {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [Dominant p] : Algebra (RationalFunction Y) (RationalFunction X) :=
  (rationalFunctionMap p).toAlgebra

/-- The algebra map of `rationalFunctionAlgebra p` is `rationalFunctionMap p`. -/
public theorem algebraMap_rationalFunctionAlgebra {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [Dominant p] :
    -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
    letI : Algebra (RationalFunction Y) (RationalFunction X) :=
      rationalFunctionAlgebra p
    algebraMap (RationalFunction Y) (RationalFunction X) =
      rationalFunctionMap p :=
  sorry

/-- The norm on rational-function units induced by a dominant morphism of
integral algebraic spaces. -/
@[expose]
public noncomputable def inducedRationalFunctionNorm {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [Dominant p] : (RationalFunction X)ˣ →* (RationalFunction Y)ˣ :=
  -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
  letI : Algebra (RationalFunction Y) (RationalFunction X) :=
    rationalFunctionAlgebra p
  Units.map (Algebra.norm (RationalFunction Y))

/-- The underlying value of the induced rational-function norm on units is the
algebra norm. -/
public theorem inducedRationalFunctionNorm_apply {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [Dominant p] (φ : (RationalFunction X)ˣ) :
    -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
    letI : Algebra (RationalFunction Y) (RationalFunction X) :=
      rationalFunctionAlgebra p
    (inducedRationalFunctionNorm p φ : RationalFunction Y) =
      Algebra.norm (RationalFunction Y) (φ : RationalFunction X) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
