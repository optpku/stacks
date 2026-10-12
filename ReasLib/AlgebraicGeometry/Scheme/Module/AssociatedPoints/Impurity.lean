/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- An impurity of a scheme module above a base point records a base change, a
specialization ending above that point, and a relative associated point of the pulled-back
module whose closure misses the fibre over the special endpoint. -/
structure Impurity (F : X.Modules) (f : X ⟶ S) (s : S) where
  /-- The scheme used for the base change. -/
  T : Scheme.{u}
  /-- The base-change morphism. -/
  g : T ⟶ S
  /-- The generic endpoint of the specialization. -/
  genericPoint : T
  /-- The special endpoint of the specialization. -/
  specialPoint : T
  /-- The chosen specialization in `T`. -/
  specializes : Specializes genericPoint specialPoint
  /-- The special endpoint lies above `s`. -/
  map_specialPoint : g specialPoint = s
  /-- The chosen point of `X ×_S T`. -/
  point : (Limits.pullback f g : Scheme)
  /-- The chosen point lies above the generic endpoint. -/
  map_point : Limits.pullback.snd f g point = genericPoint
  /-- The point belongs to the relative assassin of the pulled-back module. -/
  mem_relativeAssassin :
    point ∈ relativeAssassin (Limits.pullback.snd f g)
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F)
  /-- The closure of the chosen point misses the fibre over the special endpoint. -/
  closure_disjoint_fiber :
    Disjoint (closure {point}) ((Limits.pullback.snd f g) ⁻¹' {specialPoint})

namespace Impurity

/-- Construct an impurity from a base change, a specialization, a point of the pullback,
and the defining incidence, associated-point, and disjointness conditions. -/
def of (T : Scheme.{u}) (g : T ⟶ S) (genericPoint specialPoint : T)
    (specializes : Specializes genericPoint specialPoint)
    (map_specialPoint : g specialPoint = s)
    (point : (Limits.pullback f g : Scheme))
    (map_point : Limits.pullback.snd f g point = genericPoint)
    (mem_relativeAssassin :
      point ∈ relativeAssassin (Limits.pullback.snd f g)
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F))
    (closure_disjoint_fiber :
      Disjoint (closure {point}) ((Limits.pullback.snd f g) ⁻¹' {specialPoint})) :
    Impurity F f s where
  T := T
  g := g
  genericPoint := genericPoint
  specialPoint := specialPoint
  specializes := specializes
  map_specialPoint := map_specialPoint
  point := point
  map_point := map_point
  mem_relativeAssassin := mem_relativeAssassin
  closure_disjoint_fiber := closure_disjoint_fiber

/-- The defining specialization, point-over-base, associated-point, and disjointness
conditions carried by an impurity. -/
theorem spec (I : Impurity F f s) :
    Specializes I.genericPoint I.specialPoint ∧ I.g I.specialPoint = s ∧
      Limits.pullback.snd f I.g I.point = I.genericPoint ∧
        I.point ∈ relativeAssassin (Limits.pullback.snd f I.g)
          ((Scheme.Modules.pullback (Limits.pullback.fst f I.g)).obj F) ∧
          Disjoint (closure {I.point})
            ((Limits.pullback.snd f I.g) ⁻¹' {I.specialPoint}) := sorry

/-- Regard the pointed base change of an impurity as an étale neighbourhood when its
base-change morphism is étale. -/
def toEtaleNeighborhood (I : Impurity F f s) (h_etale : AlgebraicGeometry.Etale I.g) :
    Scheme.EtaleNeighborhood S s :=
  Scheme.EtaleNeighborhood.of (@Scheme.Etale.mk S I.T I.g h_etale)
    I.specialPoint I.map_specialPoint

/-- The étale neighbourhood attached to an impurity has the original structural map
and its selected point lies over `s`. -/
theorem toEtaleNeighborhood_spec (I : Impurity F f s)
    (h_etale : AlgebraicGeometry.Etale I.g) :
    (I.toEtaleNeighborhood h_etale).toEtale.hom = I.g ∧
      (I.toEtaleNeighborhood h_etale).toEtale.hom
        (I.toEtaleNeighborhood h_etale).point = s := sorry

/-- An impurity has elementary base change when its pointed base change determines an
elementary étale neighbourhood. -/
def IsElementary (I : Impurity F f s) : Prop :=
  ∃ h_etale : AlgebraicGeometry.Etale I.g,
    (I.toEtaleNeighborhood h_etale).IsElementary

/-- An impurity has elementary base change exactly when some étale structure on its
base-change morphism gives an elementary pointed neighbourhood. -/
theorem isElementary_iff (I : Impurity F f s) :
    I.IsElementary ↔ ∃ h_etale : AlgebraicGeometry.Etale I.g,
      (I.toEtaleNeighborhood h_etale).IsElementary := sorry

end Impurity

end AlgebraicGeometry.Scheme.Modules
