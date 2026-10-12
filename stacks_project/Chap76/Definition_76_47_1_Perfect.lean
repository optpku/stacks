/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal

/-!
# Perfect morphisms of algebraic spaces

The shared `Perfect` predicate is reused here, while the source-facing étale-local
and pointwise characterizations remain available under their original names.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Source compatibility instance retained while `Perfect` is owned by ReasLib. -/
instance isPerfectRingMap_isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) :=
  sorry

end AlgebraicGeometry.LocallyOfType

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is perfect if and only if it has the
étale-local lift of scheme-level perfectness. -/
theorem perfect_iff_etaleLocal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    Perfect f ↔
      etaleLocal
        (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) f :=
  sorry

/-- On representable algebraic spaces, perfectness recovers scheme-level
perfectness of the underlying morphism. -/
theorem perfect_ofOverMap_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    Perfect (ofOverMap h) ↔
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap h.left :=
  sorry

/-- Source-only pointwise API retained against the canonical shared `Perfect`. -/
def PerfectAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Perfect (i ≫ f)

/-- Source-only pointwise API is unfolded to its open-neighbourhood specification. -/
theorem perfectAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    PerfectAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Perfect (i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
