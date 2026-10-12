/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison.Derived
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Homology
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.FlatBaseChange
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Low-degree homology of naive cotangent base change

For a cartesian square of schemes, the canonical base-change map on naive cotangent complexes
is invertible on degree-zero homology and epic on degree-minus-one homology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace NaiveCotangent.BaseChange

variable {X X' Y Y' : _root_.AlgebraicGeometry.Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- For a cartesian square of schemes, naive-cotangent base change induces an isomorphism on
degree-zero homology. -/
theorem map_zero_isIso_of_isPullback (hpb : IsPullback g' f' f g) :
    IsIso (HomologicalComplex.homologyMap (map hpb.toCommSq) 0) := sorry

/-- For a cartesian square of schemes, naive-cotangent base change induces an epimorphism on
degree-minus-one homology. -/
theorem map_negOne_epi_of_isPullback (hpb : IsPullback g' f' f g) :
    Epi (HomologicalComplex.homologyMap (map hpb.toCommSq) (-1)) := sorry

/-- For a cartesian square of schemes whose bottom morphism is flat, the naive-cotangent
base-change map is a quasi-isomorphism. -/
theorem map_quasiIso_of_isPullback_of_flat (hpb : IsPullback g' f' f g) [Flat g] :
    QuasiIso (map hpb.toCommSq) := sorry

end NaiveCotangent.BaseChange
end AlgebraicGeometry.Scheme.Hom
