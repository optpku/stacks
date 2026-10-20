/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus

/-!
# Semistable morphisms of schemes

A morphism of schemes is semistable when it is at-worst-nodal of relative
dimension one, the unit `𝒪_S ⟶ f_* 𝒪_X` remains an isomorphism after every
base change, and every residue-field fibre has genus at least one and has no
rational tail. Properness is a separate hypothesis; together with
properness, these conditions characterize semistable families of curves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme.Hom
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The residue-field fibre of a scheme morphism, viewed as a scheme over that
residue field. -/
abbrev fibreOverField {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    SchemeOverField (S.residueField s) :=
  Over.mk (f.fiberToSpecResidueField s)

/-- The structure morphism of `fibreOverField f s` is the residue-field fibre
map of `f` at `s`. -/
theorem fibreOverField_hom {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    (fibreOverField f s).hom = f.fiberToSpecResidueField s :=
  sorry

/-- The underlying scheme of `fibreOverField f s` is the scheme-theoretic fibre
of `f` at `s`. -/
theorem fibreOverField_left {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    (fibreOverField f s).left = f.fiber s :=
  sorry

/-- A scheme over a field is a semistable fibre if it has genus at least one and
has no rational tail. -/
@[mk_iff]
class IsSemistableFibre {k : Type u} [Field k] (X : SchemeOverField k) : Prop where
  /-- The first cohomology of the structure sheaf has dimension at least one. -/
  genus_ge_one :
    1 ≤ cohomologyFinrank X.hom (unit X.left.ringCatSheaf : X.left.Modules) 1
  /-- The scheme has no rational tail. -/
  no_rational_tail : ¬ Nonempty (RationalTail X)

namespace IsSemistableFibre

/-- A semistable fibre has genus at least one and has no rational tail. -/
theorem spec {k : Type u} [Field k] (X : SchemeOverField k)
    [IsSemistableFibre X] :
    1 ≤ cohomologyFinrank X.hom (unit X.left.ringCatSheaf : X.left.Modules) 1 ∧
      ¬ Nonempty (RationalTail X) :=
  sorry

/-- On a proper one-dimensional scheme over a field with only constant global
functions, the genus bound of a semistable fibre is the arithmetic genus. -/
theorem genus {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [IsSemistableFibre X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (globalSectionsMap X.hom)) :
    1 ≤ SchemeOverField.genus X h_dimension hΓ :=
  sorry

/-- A projective smooth geometrically irreducible curve of genus at least one is
a semistable fibre. -/
theorem ofSmoothGenusGeOne {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hgenus : 1 ≤ Curve.genus X) : IsSemistableFibre X :=
  sorry

end IsSemistableFibre

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry

open SchemeOverField

/-- A morphism of schemes is semistable if it is at-worst-nodal of relative
dimension one, the unit `𝒪_S ⟶ f_* 𝒪_X` remains an isomorphism after every
base change, and every residue-field fibre is a semistable fibre.
Properness is not included in this predicate; with properness, these conditions
characterize semistable families of curves. -/
@[mk_iff]
class Semistable {X S : Scheme.{u}} (f : X ⟶ S) : Prop extends AtWorstNodal f where
  /-- The unit `𝒪_{S'} ⟶ (f ×_S S')_* 𝒪_{X ×_S S'}` is an isomorphism for every
  base change `g : S' ⟶ S`. -/
  structureSheaf_afterBaseChange :
    ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom)
  /-- Every residue-field fibre has genus at least one and has no rational
  tail. -/
  fibres_semistable : ∀ s : S, IsSemistableFibre (fibreOverField f s)

namespace Semistable

/-- A semistable morphism of schemes is at-worst-nodal of relative dimension
one. -/
instance instAtWorstNodal {X S : Scheme.{u}} (f : X ⟶ S) [h : Semistable f] :
    AtWorstNodal f :=
  h.toAtWorstNodal

/-- A semistable morphism is at-worst-nodal, the unit `𝒪_S ⟶ f_* 𝒪_X` remains
an isomorphism after every base change, and every residue-field fibre is a
semistable fibre. -/
theorem spec {X S : Scheme.{u}} (f : X ⟶ S) [Semistable f] :
    AtWorstNodal f ∧
      (∀ {S' : Scheme.{u}} (g : S' ⟶ S),
        IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom)) ∧
      ∀ s : S, IsSemistableFibre (fibreOverField f s) :=
  sorry

/-- Every residue-field fibre of a semistable morphism has genus at least
one. -/
theorem fiber_genus_ge_one {X S : Scheme.{u}} (f : X ⟶ S) [Semistable f]
    (s : S) :
    1 ≤ cohomologyFinrank (fibreOverField f s).hom
      (unit (fibreOverField f s).left.ringCatSheaf :
        (fibreOverField f s).left.Modules) 1 :=
  sorry

/-- No residue-field fibre of a semistable morphism has a rational tail. -/
theorem no_rational_tail {X S : Scheme.{u}} (f : X ⟶ S) [Semistable f]
    (s : S) : ¬ Nonempty (RationalTail (fibreOverField f s)) :=
  sorry

/-- Residue-field fibres of a semistable morphism are semistable fibres. -/
instance instIsSemistableFibre_fibreOverField {X S : Scheme.{u}} (f : X ⟶ S)
    [h : Semistable f] (s : S) : IsSemistableFibre (fibreOverField f s) :=
  h.fibres_semistable s

/-- A projective smooth geometrically irreducible curve of genus at least one
is semistable over its ground field. -/
theorem ofSmoothGenusGeOne {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hgenus : 1 ≤ Curve.genus X) : Semistable X.hom :=
  sorry

/-- A proper semistable morphism has geometrically connected fibres. -/
instance instGeometricallyConnected {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Semistable f] : GeometricallyConnected f :=
  sorry

/-- A morphism with a genus-zero residue-field fibre is not semistable. -/
theorem not_of_fiber_genus_zero {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (h : cohomologyFinrank (fibreOverField f s).hom
        (unit (fibreOverField f s).left.ringCatSheaf :
          (fibreOverField f s).left.Modules) 1 = 0) :
    ¬ Semistable f :=
  sorry

end Semistable

/-- For a proper scheme over a field, semistability of the structure morphism
is prestability together with genus at least one and the absence of a rational
tail. -/
theorem semistable_schemeOverField_iff {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom] :
    Semistable X.hom ↔
      AtWorstNodal X.hom ∧
        (∀ {S' : Scheme.{u}} (g : S' ⟶ Spec (CommRingCat.of k)),
          IsIso (commRingSheafPushforwardMap (pullback.snd X.hom g).toShHom)) ∧
        IsSemistableFibre X :=
  sorry

end AlgebraicGeometry
