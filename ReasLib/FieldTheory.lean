/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Extension.Degree
public import ReasLib.FieldTheory.Polynomial.SeparableDegree
public import ReasLib.FieldTheory.ArtinSchreier
public import ReasLib.FieldTheory.Cyclotomic.Prime
public import ReasLib.FieldTheory.Discriminant
public import ReasLib.FieldTheory.Discriminant.Quadratic
public import ReasLib.FieldTheory.Frobenius.Polynomial
public import ReasLib.FieldTheory.Frobenius.SeparableRoots
public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.FieldTheory.GeometricRegularity.FaithfullyFlat
public import ReasLib.FieldTheory.Galois.Counting
public import ReasLib.FieldTheory.Galois.KrullTopology
public import ReasLib.FieldTheory.Galois.KrullTopology.Tower
public import ReasLib.FieldTheory.Galois.Tower
public import ReasLib.FieldTheory.IsAlgClosed.Polynomial
public import ReasLib.FieldTheory.IsSepClosed.Equiv
public import ReasLib.FieldTheory.IntermediateField.GeneratorEmbedding
public import ReasLib.FieldTheory.IntermediateField.GeneratorTower
public import ReasLib.FieldTheory.IntermediateField.Adjoin.Cardinality
public import ReasLib.FieldTheory.IntermediateField.Adjoin.Generators
public import ReasLib.FieldTheory.IntermediateField.Adjoin.Simple
public import ReasLib.FieldTheory.IntermediateField.Algebraic
public import ReasLib.FieldTheory.IntermediateField.FiniteGeneration
public import ReasLib.FieldTheory.IntermediateField.SeparableTower
public import ReasLib.FieldTheory.IntermediateField.SimpleExtension
public import ReasLib.FieldTheory.Kummer.Subextension
public import ReasLib.FieldTheory.Minpoly.Charpoly
public import ReasLib.FieldTheory.Minpoly.Norm
public import ReasLib.FieldTheory.Normal.Adjoin
public import ReasLib.FieldTheory.Normal.Closure
public import ReasLib.FieldTheory.Normal.Embeddings
public import ReasLib.FieldTheory.Normal.Finite
public import ReasLib.FieldTheory.Normal.TensorProduct
public import ReasLib.FieldTheory.PurelyInseparable.FinitePthRoots
public import ReasLib.FieldTheory.PurelyInseparable.FiniteTower
public import ReasLib.FieldTheory.PurelyInseparable.Lift
public import ReasLib.FieldTheory.PurelyInseparable.Lift.Realization
public import ReasLib.FieldTheory.PurelyInseparable.OnePthRoot
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
public import ReasLib.FieldTheory.PrimeField.PowerCriterion
public import ReasLib.FieldTheory.PrimeField.PowerCriterion.ResidueField
public import ReasLib.FieldTheory.PowerGeneration
public import ReasLib.FieldTheory.RatFunc.FieldExtension
public import ReasLib.FieldTheory.RatFunc.Degree
public import ReasLib.FieldTheory.RatFunc.FiniteGeneration
public import ReasLib.FieldTheory.Separable.DiagonalLocalization
public import ReasLib.FieldTheory.Separable.Generated.Frobenius
public import ReasLib.FieldTheory.Separable.Generated.GeometricallyReduced
public import ReasLib.FieldTheory.Separable.Generated.TensorProduct
public import ReasLib.FieldTheory.Separable.Generated.CharZero
public import ReasLib.FieldTheory.Separable.Generated.GeometricallyNormal
public import ReasLib.FieldTheory.Separable.Generated.OnePthRoot
public import ReasLib.FieldTheory.Separable.Generated.Primitive
public import ReasLib.FieldTheory.Separable.Generated.Properties
public import ReasLib.FieldTheory.SeparableClosure.Map
public import ReasLib.FieldTheory.SeparableDegree.Embeddings
public import ReasLib.FieldTheory.TensorProduct.CommonOverfield
public import ReasLib.FieldTheory.TensorProduct.Galois
public import ReasLib.FieldTheory.TensorProduct.Separable
public import ReasLib.FieldTheory.TensorProduct.SeparableClosure
public import ReasLib.FieldTheory.Transcendence.FiniteType
public import ReasLib.FieldTheory.Transcendence.OneVariable
public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental

/-!
# Reusable field-theory support

This module collects project-level field-theory constructions whose mathematical ownership is
independent of any numbered textbook chapter.
-/
