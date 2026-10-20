module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-! # Conservativity of formal glueing of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-- For a quasi-compact, quasi-separated morphism `f : Y ⟶ X` and a
finite-presentation closed immersion `i : Z ⟶ X` satisfying the formal-glueing
conditions, the canonical functor `Over X ⥤ category f i` reflects isomorphisms. -/
instance functor_reflectsIsomorphisms {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (functor f i).ReflectsIsomorphisms :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing
