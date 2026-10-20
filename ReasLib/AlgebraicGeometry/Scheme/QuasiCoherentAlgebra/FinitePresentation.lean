module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QcAlgebraUnder

/-- The property of an algebra sheaf of being quasi-coherent and finitely presentable. -/
abbrev finitelyPresentableProperty (S : Scheme.{u}) :
    ObjectProperty (Under (schemeCommRingSheaf S)) :=
  fun B ↦ qcAlgebraUnderProperty S B ∧ IsFinitelyPresentable.{u} B

/-- Every quasi-coherent algebra sheaf on a quasi-compact quasi-separated scheme is a filtered
colimit of quasi-coherent finitely presentable algebra sheaves. -/
theorem finitelyPresentable_ind
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (A : S.QcAlgebraUnder) :
    (finitelyPresentableProperty S).ind.{u} A.obj := sorry

end AlgebraicGeometry.Scheme.QcAlgebraUnder

end
