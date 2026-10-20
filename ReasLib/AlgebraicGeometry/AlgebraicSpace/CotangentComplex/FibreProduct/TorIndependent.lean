/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.FibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence
public import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-independent fibre products and cotangent complexes of algebraic spaces

For Tor-independent algebraic spaces over a common base, the canonical cotangent
comparison sum map is an isomorphism and its cone vanishes.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent
namespace FibreProduct

/-- The canonical fibre-product cotangent comparison cone vanishes for
Tor-independent algebraic spaces over a common base. -/
@[stacks 09DL]
theorem cone_isZero_of_torIndependent {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B)
    (h_torIndependent : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsZero (cone f g) :=
  sorry

/-- The canonical sum map from the two pulled-back cotangent complexes to the
cotangent complex of a fibre product is an isomorphism under Tor independence. -/
@[stacks 09DL]
theorem sumMap_isIso_of_torIndependent {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B)
    (h_torIndependent : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIso (sumMap f g) :=
  sorry

/-- The cotangent complex of a Tor-independent fibre product is isomorphic in
the derived category to the biproduct of the two pulled-back cotangent complexes. -/
theorem isIsomorphic_cotangent_sumMapSource_of_torIndependent
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (h_torIndependent : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIsomorphic (cotangent (toBase f g))
      (DerivedCategory.Q.obj
        (pullbackCotangentCochain (pullback.fst f g) f ⊞
          pullbackCotangentCochain (pullback.snd f g) g)) :=
  sorry

/-- The canonical fibre-product cotangent sum map is an isomorphism whenever
Tor independence is available through `Fact`. -/
instance sumMap_isIso_of_fact_torIndependent
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    [Fact (TorIndependentOver (Over.mk f) (Over.mk g))] :
    IsIso (sumMap f g) :=
  sumMap_isIso_of_torIndependent f g Fact.out

end FibreProduct
end AlgebraicGeometry.AlgebraicSpace.Cotangent
