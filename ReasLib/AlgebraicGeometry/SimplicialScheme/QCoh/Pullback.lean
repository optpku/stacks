/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Quasi-coherent pullback along a morphism of simplicial schemes

Restriction of `modulePullback` to the full subcategory of quasi-coherent
modules on the Zariski ringed site of a simplicial scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

namespace QCoh

/-- Pullback of quasi-coherent modules along a morphism of simplicial schemes. -/
noncomputable def pullback {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    QCoh U ⥤ QCoh V :=
  FullSubcategory.restrict (modulePullback f) (modulePullback_le_inverseImage f)

/-- The underlying module sheaf of a pulled-back quasi-coherent module is the
usual module pullback. -/
theorem pullback_obj {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    (F : QCoh U) :
    ((pullback f).obj F).obj = (modulePullback f).obj F.obj :=
  sorry

/-- Forgetting quasi-coherence after restricted pullback recovers ambient
module-sheaf pullback. -/
noncomputable def pullback.inclusionIso {V U : SimplicialObject Scheme.{u}}
    (f : V ⟶ U) :
    pullback f ⋙ inclusion V ≅ inclusion U ⋙ modulePullback f :=
  FullSubcategory.restrict.compιIso (modulePullback f) (modulePullback_le_inverseImage f)

end QCoh

end AlgebraicGeometry.SimplicialObject
