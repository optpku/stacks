/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import stacks_project.Chap109.Definition_109_21_2_Semistable

/-!
# Stable morphisms of schemes

A morphism of schemes is a stable family of curves when it is at-worst-nodal
of relative dimension one, the unit `𝒪_S ⟶ f_* 𝒪_X` remains an isomorphism
after every base change, and every residue-field fibre has genus at least two
and has neither a rational tail nor a rational bridge.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme.Hom
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A scheme over a field is a stable fibre if it has genus at least two and
has neither a rational tail nor a rational bridge. -/
@[mk_iff]
class IsStableFibre {k : Type u} [Field k] (X : SchemeOverField k) : Prop where
  /-- The first cohomology of the structure sheaf has dimension at least two. -/
  genus_ge_two :
    2 ≤ cohomologyFinrank X.hom (unit X.left.ringCatSheaf : X.left.Modules) 1
  /-- The scheme has no rational tail. -/
  no_rational_tail : ¬ Nonempty (RationalTail X)
  /-- The scheme has no rational bridge. -/
  no_rational_bridge : ¬ Nonempty (RationalBridge X)

namespace IsStableFibre

/-- A stable fibre has genus at least two and has neither a rational tail nor a
rational bridge. -/
theorem spec {k : Type u} [Field k] (X : SchemeOverField k)
    [IsStableFibre X] :
    2 ≤ cohomologyFinrank X.hom (unit X.left.ringCatSheaf : X.left.Modules) 1 ∧
      ¬ Nonempty (RationalTail X) ∧ ¬ Nonempty (RationalBridge X) :=
  sorry

/-- On a proper one-dimensional scheme over a field with only constant global
functions, the genus bound of a stable fibre is the arithmetic genus. -/
theorem genus {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [IsStableFibre X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (globalSectionsMap X.hom)) :
    2 ≤ SchemeOverField.genus X h_dimension hΓ :=
  sorry

/-- A stable fibre is a semistable fibre. -/
instance instIsSemistableFibre {k : Type u} [Field k] (X : SchemeOverField k)
    [IsStableFibre X] : IsSemistableFibre X :=
  sorry

/-- A projective smooth geometrically irreducible curve of genus at least two
is a stable fibre. -/
theorem ofSmoothGenusGeTwo {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hgenus : 2 ≤ Curve.genus X) : IsStableFibre X :=
  sorry

end IsStableFibre

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry

open SchemeOverField

/-- A morphism of schemes is a stable family if it is at-worst-nodal of relative
dimension one, the unit `𝒪_S ⟶ f_* 𝒪_X` remains an isomorphism after every
base change, and every residue-field fibre is a stable fibre. -/
@[mk_iff]
class IsStableFamily {X S : Scheme.{u}} (f : X ⟶ S) : Prop extends AtWorstNodal f where
  /-- The unit `𝒪_{S'} ⟶ (f ×_S S')_* 𝒪_{X ×_S S'}` is an isomorphism for every
  base change `g : S' ⟶ S`. -/
  structureSheaf_afterBaseChange :
    ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom)
  /-- Every residue-field fibre has genus at least two and has neither a
  rational tail nor a rational bridge. -/
  fibres_stable : ∀ s : S, IsStableFibre (fibreOverField f s)

namespace IsStableFamily

/-- A stable family of schemes is at-worst-nodal of relative dimension
one. -/
instance instAtWorstNodal {X S : Scheme.{u}} (f : X ⟶ S) [h : IsStableFamily f] :
    AtWorstNodal f :=
  h.toAtWorstNodal

/-- A stable family of schemes is semistable. -/
instance instSemistable {X S : Scheme.{u}} (f : X ⟶ S) [IsStableFamily f] :
    Semistable f :=
  sorry

/-- A stable family is at-worst-nodal, the unit `𝒪_S ⟶ f_* 𝒪_X` remains an
isomorphism after every base change, and every residue-field fibre is a stable
fibre. -/
theorem spec {X S : Scheme.{u}} (f : X ⟶ S) [IsStableFamily f] :
    AtWorstNodal f ∧
      (∀ {S' : Scheme.{u}} (g : S' ⟶ S),
        IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom)) ∧
      ∀ s : S, IsStableFibre (fibreOverField f s) :=
  sorry

/-- Every residue-field fibre of a stable family has genus at least two. -/
theorem fiber_genus_ge_two {X S : Scheme.{u}} (f : X ⟶ S) [IsStableFamily f] (s : S) :
    2 ≤ cohomologyFinrank (fibreOverField f s).hom
      (unit (fibreOverField f s).left.ringCatSheaf :
        (fibreOverField f s).left.Modules) 1 :=
  sorry

/-- No residue-field fibre of a stable family has a rational tail. -/
theorem no_rational_tail {X S : Scheme.{u}} (f : X ⟶ S) [IsStableFamily f] (s : S) :
    ¬ Nonempty (RationalTail (fibreOverField f s)) :=
  sorry

/-- No residue-field fibre of a stable family has a rational bridge. -/
theorem no_rational_bridge {X S : Scheme.{u}} (f : X ⟶ S) [IsStableFamily f] (s : S) :
    ¬ Nonempty (RationalBridge (fibreOverField f s)) :=
  sorry

/-- A projective smooth geometrically irreducible curve of genus at least two
is a stable family over its ground field. -/
theorem ofSmoothGenusGeTwo {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hgenus : 2 ≤ Curve.genus X) : IsStableFamily X.hom :=
  sorry

/-- A proper stable family has geometrically connected fibres. -/
instance instGeometricallyConnected {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsStableFamily f] : GeometricallyConnected f :=
  sorry

/-- A prestable family of genus `0` or `1` is never a stable family. -/
theorem not_of_fiber_genus_lt_two {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (h : cohomologyFinrank (fibreOverField f s).hom
        (unit (fibreOverField f s).left.ringCatSheaf :
          (fibreOverField f s).left.Modules) 1 < 2) :
    ¬ IsStableFamily f :=
  sorry

end IsStableFamily

/-- For a proper scheme over a field, stability of the structure morphism is
prestability together with genus at least two and the absence of rational
tails and rational bridges. -/
theorem stable_schemeOverField_iff {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom] :
    IsStableFamily X.hom ↔
      AtWorstNodal X.hom ∧
        (∀ {S' : Scheme.{u}} (g : S' ⟶ Spec (CommRingCat.of k)),
          IsIso (commRingSheafPushforwardMap (pullback.snd X.hom g).toShHom)) ∧
        IsStableFibre X :=
  sorry

end AlgebraicGeometry
