module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FieldExtension

/-- The projection from base change along a purely inseparable field extension is a universal
homeomorphism. -/
instance instToSourceUniversalHomeomorphism
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    UniversalHomeomorphism (toSource k K f) := sorry

end AlgebraicGeometry.FieldExtension
