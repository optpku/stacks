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

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace Impurity

variable {X S : Scheme.{u}} {F : X.Modules} {f : X ⟶ S} {s : S}

/-- The canonical map from the pullback along an impurity's base change to the pullback
along a compatible factorization of that base change. -/
noncomputable def baseChangeMap (J : Impurity F f s) {T' : Scheme.{u}} (g' : T' ⟶ S)
    (p : J.T ⟶ T') (hp : p ≫ g' = J.g) :
    Limits.pullback f J.g ⟶ Limits.pullback f g' :=
  Limits.pullback.map f J.g f g' (𝟙 X) p (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id J.g).trans hp.symm)

/-- The canonical comparison map preserves the projection to the source scheme. -/
theorem baseChangeMap_fst (J : Impurity F f s) {T' : Scheme.{u}} (g' : T' ⟶ S)
    (p : J.T ⟶ T') (hp : p ≫ g' = J.g) :
    J.baseChangeMap g' p hp ≫ Limits.pullback.fst f g' = Limits.pullback.fst f J.g := sorry

/-- The canonical comparison map carries the second projection through the factorization. -/
theorem baseChangeMap_snd (J : Impurity F f s) {T' : Scheme.{u}} (g' : T' ⟶ S)
    (p : J.T ⟶ T') (hp : p ≫ g' = J.g) :
    J.baseChangeMap g' p hp ≫ Limits.pullback.snd f g' =
      Limits.pullback.snd f J.g ≫ p := sorry

/-- The canonical images of an impurity's points along a compatible factorization satisfy
the impurity conditions over the factorized base-change morphism. -/
structure DescendsAlong (J : Impurity F f s) {T' : Scheme.{u}} (g' : T' ⟶ S)
    (p : J.T ⟶ T') (hp : p ≫ g' = J.g) : Prop where
  /-- The images of the endpoints remain a specialization. -/
  specializes : Specializes (p J.genericPoint) (p J.specialPoint)
  /-- The image of the special endpoint remains over the original base point. -/
  map_specialPoint : g' (p J.specialPoint) = s
  /-- The transported pullback point lies over the image of the generic endpoint. -/
  map_point :
    Limits.pullback.snd f g' (J.baseChangeMap g' p hp J.point) = p J.genericPoint
  /-- The transported pullback point belongs to the relative assassin at the target. -/
  mem_relativeAssassin :
    J.baseChangeMap g' p hp J.point ∈ relativeAssassin (Limits.pullback.snd f g')
      ((Scheme.Modules.pullback (Limits.pullback.fst f g')).obj F)
  /-- The closure of the transported point misses the fibre over the special endpoint. -/
  closure_disjoint_fiber :
    Disjoint (closure {J.baseChangeMap g' p hp J.point})
      ((Limits.pullback.snd f g') ⁻¹' {p J.specialPoint})

/-- Descent along a compatible factorization is equivalent to its specialization, incidence,
relative-assassin, and fibre-disjointness conditions. -/
theorem descendsAlong_iff (J : Impurity F f s) {T' : Scheme.{u}} (g' : T' ⟶ S)
    (p : J.T ⟶ T') (hp : p ≫ g' = J.g) :
    J.DescendsAlong g' p hp ↔
      Specializes (p J.genericPoint) (p J.specialPoint) ∧
        g' (p J.specialPoint) = s ∧
          Limits.pullback.snd f g' (J.baseChangeMap g' p hp J.point) = p J.genericPoint ∧
            J.baseChangeMap g' p hp J.point ∈ relativeAssassin (Limits.pullback.snd f g')
              ((Scheme.Modules.pullback (Limits.pullback.fst f g')).obj F) ∧
              Disjoint (closure {J.baseChangeMap g' p hp J.point})
                ((Limits.pullback.snd f g') ⁻¹' {p J.specialPoint}) := sorry

namespace DescendsAlong

/-- Turn projection-compatible descent data into the corresponding impurity over the
factorized base-change morphism. -/
noncomputable def toImpurity (J : Impurity F f s) {T' : Scheme.{u}} {g' : T' ⟶ S}
    {p : J.T ⟶ T'} {hp : p ≫ g' = J.g} (h : J.DescendsAlong g' p hp) :
    Impurity F f s where
  T := T'
  g := g'
  genericPoint := p J.genericPoint
  specialPoint := p J.specialPoint
  specializes := h.specializes
  map_specialPoint := h.map_specialPoint
  point := J.baseChangeMap g' p hp J.point
  map_point := h.map_point
  mem_relativeAssassin := h.mem_relativeAssassin
  closure_disjoint_fiber := h.closure_disjoint_fiber

/-- The generic endpoint of the descended impurity is the transported generic endpoint. -/
theorem toImpurity_genericPoint (J : Impurity F f s) {T' : Scheme.{u}} {g' : T' ⟶ S}
    {p : J.T ⟶ T'} {hp : p ≫ g' = J.g} (h : J.DescendsAlong g' p hp) :
    (h.toImpurity J).genericPoint = p J.genericPoint := sorry

/-- The pullback point of the descended impurity is the canonical image of the original
pullback point. -/
theorem toImpurity_point (J : Impurity F f s) {T' : Scheme.{u}} {g' : T' ⟶ S}
    {p : J.T ⟶ T'} {hp : p ≫ g' = J.g} (h : J.DescendsAlong g' p hp) :
    (h.toImpurity J).point = J.baseChangeMap g' p hp J.point := sorry

end DescendsAlong

end Impurity
end Modules
end Scheme
end AlgebraicGeometry
