/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Base
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed colimits in `CommAlgCat`

This leaf presents the explicit ring direct limit of a preorder-indexed diagram of
commutative algebras as a cocone in `CommAlgCat`.  The algebra structure is a
named construction rather than a global instance: the diagram determines it,
but a bare direct-limit carrier does not retain that diagram as typeclass data.
The stage and index universes are independent; only the cocone-level owner
raises the stage universe to the index level so its apex remains in the same
`CommAlgCat`.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w z

noncomputable section

namespace CommAlgCat.DirectLimit

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I]

/-- The underlying ring of the direct limit of a preorder-indexed diagram of
commutative `R`-algebras. -/
@[stacks 00QV "commutative-algebra direct limit"]
abbrev ring (F : I ⥤ CommAlgCat.{w} R) : Type max w v :=
  Ring.DirectLimit (fun i ↦ ↑(F.obj i))
    (fun _ _ h ↦ (F.map (homOfLE h)).hom)

/-- The canonical `R`-algebra structure on `ring F`, induced by the algebra
structures and transition maps of `F`.  It is explicit so callers do not
silently select an unrelated action on the same carrier. -/
@[reducible, stacks 00QV "commutative-algebra direct limit"]
noncomputable def algebra [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) : Algebra R (ring F) :=
  Ring.DirectLimit.algebra
    (fun i ↦ ↑(F.obj i))
    (fun _ _ h ↦ (F.map (homOfLE h)).hom)

/-- The canonical `R`-algebra map from a stage of a directed diagram to its
explicit direct limit. -/
@[stacks 00QV "commutative-algebra direct limit"]
noncomputable def of [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) (i : I) :
    letI : Algebra R (ring F) := algebra F
    ↑(F.obj i) →ₐ[R] ring F :=
  letI : Algebra R (ring F) := algebra F
  Ring.DirectLimit.ofAlgHom
    (fun i ↦ ↑(F.obj i))
    (fun _ _ h ↦ (F.map (homOfLE h)).hom) i

/-- The canonical algebra map from a stage evaluates through the underlying
ring direct-limit map. -/
@[simp, stacks 00QV "commutative-algebra direct limit"]
theorem of_apply [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) (i : I) (x : F.obj i) :
    letI : Algebra R (ring F) := algebra F
    of F i x = Ring.DirectLimit.of (fun i ↦ ↑(F.obj i))
      (fun _ _ h ↦ (F.map (homOfLE h)).hom) i x := sorry

/-- The stage maps into the explicit direct limit respect every transition of
the directed diagram. -/
@[stacks 00QV "commutative-algebra direct limit"]
theorem of_comp [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) {i j : I} (h : i ≤ j) :
    letI : Algebra R (ring F) := algebra F
    (of F j).comp (F.map (homOfLE h)).hom = of F i := sorry

/-- The canonical stage maps commute pointwise with every transition of the
directed algebra diagram. -/
@[simp, stacks 00QV "commutative-algebra direct limit"]
theorem of_map [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) {i j : I} (h : i ≤ j)
    (x : F.obj i) :
    letI : Algebra R (ring F) := algebra F
    of F j ((F.map (homOfLE h)).hom x) = of F i x := sorry

/-- The canonical descent map from the explicit direct limit of a directed
diagram of `R`-algebras to any cocone over that diagram. -/
@[stacks 00QV "commutative-algebra direct limit"]
noncomputable def desc [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) (s : Cocone F) :
    letI : Algebra R (ring F) := algebra F
    ring F →ₐ[R] s.pt :=
  letI : Algebra R (ring F) := algebra F
  Ring.DirectLimit.liftAlgHom
    (fun i ↦ ↑(F.obj i))
    (fun _ _ h ↦ (F.map (homOfLE h)).hom)
    (fun i ↦ (s.ι.app i).hom)
    (fun i j h ↦ by
      exact congrArg (fun g : F.obj i ⟶ s.pt ↦ g.hom) (s.w (homOfLE h)))

/-- The direct-limit descent map agrees with the specified cocone leg on a
representative from any stage. -/
@[stacks 00QV "commutative-algebra direct limit"]
theorem desc_of [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) (s : Cocone F) (i : I)
    (x : F.obj i) :
    letI : Algebra R (ring F) := algebra F
    desc F s
        (Ring.DirectLimit.of (fun i ↦ ↑(F.obj i))
          (fun _ _ h ↦ (F.map (homOfLE h)).hom) i x) =
      (s.ι.app i).hom x := sorry

/-- The descent algebra homomorphism restricts to the corresponding cocone
leg at every stage. -/
@[simp, stacks 00QV "commutative-algebra direct limit"]
theorem desc_comp_of [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) (s : Cocone F) (i : I) :
    letI : Algebra R (ring F) := algebra F
    (desc F s).comp (of F i) = (s.ι.app i).hom := sorry

/-- Algebra morphisms from the explicit direct limit are determined by their
restrictions to every stage. -/
@[stacks 00QV "commutative-algebra direct limit"]
theorem algHom_ext [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{w} R) {S : Type z}
    [CommRing S] [Algebra R S]
    {g h :
      letI : Algebra R (ring F) := algebra F
      ring F →ₐ[R] S}
    (h_stage : ∀ i,
      letI : Algebra R (ring F) := algebra F
      g.comp (of F i) = h.comp (of F i)) :
    g = h := sorry

/-- The explicit direct limit together with its stage maps forms a cocone in
`CommAlgCat R`.  The object universe is `max w v` so that the direct-limit
carrier and the cocone apex live in the same category universe. -/
@[stacks 00QV "commutative-algebra direct limit"]
noncomputable def cocone
    {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (F : J ⥤ CommAlgCat.{max w v} R) : Cocone F :=
  letI : Algebra R (ring F) := algebra F
  { pt := CommAlgCat.of R (ring F)
    ι :=
      { app := fun i ↦ CommAlgCat.ofHom (of F i)
        naturality := sorry } }

/-- The explicit direct-limit cocone is colimiting in `CommAlgCat R`.  Its
descent map is the direct-limit algebra-hom lift; only the universal-property
proof fields remain deferred at the statement stage. -/
@[stacks 00QV "commutative-algebra direct limit"]
noncomputable def isColimit
    {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (F : J ⥤ CommAlgCat.{max w v} R) :
    IsColimit (cocone F) :=
  letI : Algebra R (ring F) := algebra F
  { desc := fun s ↦
      CommAlgCat.ofHom (desc F s)
    fac := sorry
    uniq := sorry }

end CommAlgCat.DirectLimit
