/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Generic-point normalization prerequisites over a field

This leaf supplies the canonical finiteness and separation instances that let
the generic-point normalization construction operate on a scheme locally of
finite type over a field. The reduction and reduced irreducible-component
instances are kept here because they are the same prerequisites for the
normalization comparison maps, rather than chapter-specific consequences.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization

variable {k : Type u} [Field k]

namespace FiniteComponents

/-- A scheme locally of finite type over a field has finitely many irreducible
components on every quasi-compact open. -/
instance instOnCompactOpens
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X.left := sorry

end FiniteComponents

namespace GenericPoints

/-- The generic-point residue-field coproduct of a scheme locally of finite
type over a field is quasi-compact. -/
instance instCoproductQuasiCompact
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    QuasiCompact (genericPointSpectrumCoproductTo X.left) := sorry

/-- The generic-point residue-field coproduct of a scheme locally of finite
type over a field is quasi-separated. -/
instance instCoproductQuasiSeparated
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    QuasiSeparated (genericPointSpectrumCoproductTo X.left) := sorry

end GenericPoints

namespace Reduction

/-- The reduction of a scheme locally of finite type over a field remains
locally of finite type over that field. -/
instance instLocallyOfFiniteType
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (X.left.nilradical.subschemeι ≫ X.hom) := sorry

namespace GenericPoints

/-- The generic-point residue-field coproduct of the reduction of a scheme
locally of finite type over a field is quasi-compact. -/
instance instCoproductQuasiCompact
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    QuasiCompact (genericPointSpectrumCoproductTo X.left.nilradical.subscheme) := sorry

/-- The generic-point residue-field coproduct of the reduction of a scheme
locally of finite type over a field is quasi-separated. -/
instance instCoproductQuasiSeparated
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    QuasiSeparated (genericPointSpectrumCoproductTo X.left.nilradical.subscheme) := sorry

end GenericPoints
end Reduction

namespace IrreducibleComponent

/-- A reduced irreducible-component subscheme of a scheme locally of finite
type over a field remains locally of finite type over that field. -/
instance instLocallyOfFiniteType
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (Z : irreducibleComponents X.left) :
    LocallyOfFiniteType (X.left.irreducibleComponentSubschemeι Z ≫ X.hom) := sorry

namespace GenericPoints

/-- The generic-point residue-field coproduct of a reduced
irreducible-component subscheme over a field is quasi-compact. -/
instance instCoproductQuasiCompact
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (Z : irreducibleComponents X.left) :
    QuasiCompact (genericPointSpectrumCoproductTo
      (X.left.irreducibleComponentSubscheme Z)) := sorry

/-- The generic-point residue-field coproduct of a reduced
irreducible-component subscheme over a field is quasi-separated. -/
instance instCoproductQuasiSeparated
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (Z : irreducibleComponents X.left) :
    QuasiSeparated (genericPointSpectrumCoproductTo
      (X.left.irreducibleComponentSubscheme Z)) := sorry

end GenericPoints
end IrreducibleComponent

end AlgebraicGeometry.SchemeOverField.Normalization
