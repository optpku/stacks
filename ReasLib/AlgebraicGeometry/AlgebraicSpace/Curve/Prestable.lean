/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Nodal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.H0Dim1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom

/-!
# Prestable families of curves

A family of curves is prestable when it is at-worst-nodal of relative
dimension 1 and the canonical unit `𝒪_Y ⟶ f_* 𝒪_X` remains an isomorphism
after every base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is prestable if it is a family
of curves, is at-worst-nodal of relative dimension 1, and the canonical unit
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism after every base change. -/
@[mk_iff]
class Prestable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends Spaces.Curves.IsFamily f, AtWorstNodal f where
  /-- The unit `𝒪_Z ⟶ (f ×_Y Z)_* 𝒪_{X ×_Y Z}` is an isomorphism for every
  base change `g : Z ⟶ Y`. -/
  universallyUnitToPushforwardObjUnit_isIso :
    ∀ {Z : AlgebraicSpace S} (g : Z ⟶ Y),
      IsIso (Modules.unitToPushforwardObjUnit (pullback.snd f g))

namespace Prestable

/-- A prestable morphism is a family of curves, is at-worst-nodal of relative
dimension 1, and has universally invertible canonical structure-sheaf unit. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [h : Prestable f] :
    Spaces.Curves.IsFamily f ∧ AtWorstNodal f ∧
      ∀ {Z : AlgebraicSpace S} (g : Z ⟶ Y),
        IsIso (Modules.unitToPushforwardObjUnit (pullback.snd f g)) :=
  ⟨h.toIsFamily, h.toAtWorstNodal, h.universallyUnitToPushforwardObjUnit_isIso⟩

end Prestable

/-- A proper geometrically connected at-worst-nodal morphism of schemes over
`S` is prestable as a morphism of algebraic spaces. -/
instance instPrestable_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.AtWorstNodal h.left] [IsProper h.left]
    [GeometricallyConnected h.left] : Prestable (ofOverMap h) :=
  sorry

/-- The second projection of a pullback of a prestable morphism is prestable. -/
instance instPrestable_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Prestable f] : Prestable (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of prestable families of curves. -/
def prestable (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ Prestable (hom P)

/-- Membership in `prestable` is prestability of the structure morphism. -/
theorem prestable_iff {S : Scheme.{u}} (P : Obj S) :
    prestable S P ↔ Prestable (hom P) :=
  Iff.rfl

/-- A family of curves is prestable precisely when it is nodal and has
universally trivial structure-sheaf pushforward and fibres of dimension one. -/
theorem prestable_iff_nodal_h0Dim1 {S : Scheme.{u}} (P : Obj S) :
    prestable S P ↔ nodal S P ∧ h0Dim1 S P :=
  sorry

/-- Prestability of families of curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_prestable (S : Scheme.{u}) :
    (prestable S).IsClosedUnderIsomorphisms :=
  sorry

/-- For every family of curves, an open of its base represents prestability
under every cartesian morphism of families. -/
theorem exists_prestable_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      prestable S Q ↔ Set.range (baseMap φ).left ⊆ U :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a prestable
family precisely when its singularities are at-worst-nodal, its dimension is
one, and its canonical map on global sections is bijective. -/
@[stacks 0E6U]
theorem classifying_factorsThrough_prestable_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    prestable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
