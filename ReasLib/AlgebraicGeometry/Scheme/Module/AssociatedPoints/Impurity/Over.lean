/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Impurity

/-- An impurity whose base-change morphism and special point have been fixed in
advance. -/
structure Over.{u} {X S T : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (s : S)
    (g : T ⟶ S) (t : T) where
  /-- The generic endpoint of the specialization. -/
  genericPoint : T
  /-- The chosen specialization to the fixed special point. -/
  specializes : Specializes genericPoint t
  /-- The fixed special point lies over `s`. -/
  map_specialPoint : g t = s
  /-- The chosen point of `X ×_S T`. -/
  point : (Limits.pullback f g : Scheme)
  /-- The chosen point lies above the generic endpoint. -/
  map_point : Limits.pullback.snd f g point = genericPoint
  /-- The point belongs to the relative assassin of the pulled-back module. -/
  mem_relativeAssassin :
    point ∈ relativeAssassin (Limits.pullback.snd f g)
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F)
  /-- The closure of the chosen point misses the fibre over the fixed special point. -/
  closure_disjoint_fiber :
    Disjoint (closure {point}) ((Limits.pullback.snd f g) ⁻¹' {t})

universe u

variable {X S T : Scheme.{u}}

namespace Over

/-- The defining specialization, point-over-base, associated-point, and disjointness
conditions carried by an impurity over a fixed pointed base change. -/
theorem spec {F : X.Modules} {f : X ⟶ S} {s : S} {g : T ⟶ S} {t : T}
    (I : Impurity.Over F f s g t) :
    Specializes I.genericPoint t ∧ g t = s ∧
      Limits.pullback.snd f g I.point = I.genericPoint ∧
        I.point ∈ relativeAssassin (Limits.pullback.snd f g)
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F) ∧
          Disjoint (closure {I.point}) ((Limits.pullback.snd f g) ⁻¹' {t}) := sorry

/-- Forget the fixed-base indexing of an impurity while retaining all of its data. -/
def toImpurity {F : X.Modules} {f : X ⟶ S} {s : S} {g : T ⟶ S} {t : T}
    (I : Impurity.Over F f s g t) : Impurity F f s where
  T := T
  g := g
  genericPoint := I.genericPoint
  specialPoint := t
  specializes := I.specializes
  map_specialPoint := I.map_specialPoint
  point := I.point
  map_point := I.map_point
  mem_relativeAssassin := I.mem_relativeAssassin
  closure_disjoint_fiber := I.closure_disjoint_fiber

end Over

end AlgebraicGeometry.Scheme.Modules.Impurity
