/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism

/-!
# Rational-function maps of dominant morphisms

A dominant morphism of integral algebraic spaces induces a homomorphism on
rational-function fields by residue-field transport at the unique generic point.
The associated algebra structure is explicit and depends on the morphism.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

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

/-- At every generic point of the source, the induced rational-function map is
residue-field transport through the generic-point evaluation equivalences. -/
public theorem rationalFunctionMap_spec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [Dominant p] {η : Points X} (hη : η ∈ genericPoints X) :
    rationalFunctionMap p =
      (rationalFunctionRingEquivResidueField hη).symm.toRingHom.comp
        ((RingHom.ulift.{u + 1, u + 1} (residueFieldMap p η).hom).comp
          (rationalFunctionRingEquivResidueField
            (map_mem_genericPoints_of_isDominant p hη)).toRingHom) :=
  sorry

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

end AlgebraicGeometry.AlgebraicSpace.Hom
