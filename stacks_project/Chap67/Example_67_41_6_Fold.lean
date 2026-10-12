/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Example_65_14_2_Descent

/-!
# Quasi-compactness and universal closedness of the doubled-origin fold

The identified base change of the Galois-twist structure morphism along the finite
étale cover `U ⟶ 𝔸¹_k` is the fold of the affine line with doubled origin. This
module records that the fold and `Spec(k') ⟶ Spec(k)` are quasi-compact and/or
universally closed, and that the base-change projection of `π` along `U ⟶ 𝔸¹_k`
is representably quasi-compact and universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.DoubledOrigin

/-- The fold from affine line with doubled origin to the affine line is
quasi-compact. -/
instance instQuasiCompact_fold (k : Type u) [Field k] :
    QuasiCompact (fold k 1) := sorry

/-- The fold from affine line with doubled origin to the affine line is
universally closed. -/
instance instUniversallyClosed_fold (k : Type u) [Field k] :
    UniversallyClosed (fold k 1) := sorry

end AlgebraicGeometry.DoubledOrigin

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/-- Affine line with doubled origin, viewed as a scheme over `𝔸¹_k` via the fold
followed by `U ⟶ 𝔸¹_k`. -/
def doubledOriginAsOver (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Over (base k) :=
  Over.mk ((doubledOriginOver k k').hom ≫ (cover k k').hom)

/-- `doubledOriginAsOver` is classified by the composite of the fold with the cover. -/
theorem doubledOriginAsOver_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    doubledOriginAsOver k k' =
      Over.mk ((doubledOriginOver k k').hom ≫ (cover k k').hom) :=
  sorry

/-- The composite of the doubled-origin fold with `U ⟶ 𝔸¹_k` agrees with the
structure morphism of `doubledOriginAsOver`. -/
theorem doubledOriginToCover_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (doubledOriginOver k k').hom ≫ (cover k k').hom =
      (doubledOriginAsOver k k').hom :=
  sorry

/-- The fold `doubledOriginOver.hom`, as a morphism over `𝔸¹_k`. -/
def doubledOriginToCover (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    doubledOriginAsOver k k' ⟶ cover k k' :=
  Over.homMk (doubledOriginOver k k').hom (doubledOriginToCover_w k k')

/-- The underlying scheme morphism of `doubledOriginToCover` is the identified
base-change fold. -/
theorem doubledOriginToCover_left (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (doubledOriginToCover k k').left = (doubledOriginOver k k').hom :=
  sorry

/-- The base-change projection of `π : X ⟶ 𝔸¹_k` along the étale-surjective cover
`U ⟶ 𝔸¹_k`. -/
def structureHomPullback (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Limits.pullback (structureHom k k' hdeg)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (coverToBase k k')) ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k k') :=
  Limits.pullback.snd (structureHom k k' hdeg)
    ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (coverToBase k k'))

/-- `structureHomPullback` is the second projection of the pullback of `π` along
`U ⟶ 𝔸¹_k`. -/
theorem structureHomPullback_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    structureHomPullback k k' hdeg =
      Limits.pullback.snd (structureHom k k' hdeg)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (coverToBase k k')) :=
  sorry

/-- The base change of `X` along `U ⟶ 𝔸¹_k` is the doubled-origin line over `𝔸¹_k`. -/
theorem structureHomPullback_iso (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Nonempty
      (Limits.pullback (structureHom k k' hdeg)
          ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (coverToBase k k')) ≅
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj
          (doubledOriginAsOver k k')) :=
  sorry

/-- The base-change projection of `π` along the étale-surjective cover `U ⟶ 𝔸¹_k`
is representably quasi-compact. -/
theorem quasiCompact_structureHom (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (structureHomPullback k k' hdeg).hom :=
  sorry

/-- The base-change projection of `π` along the étale-surjective cover `U ⟶ 𝔸¹_k`
is representably universally closed. -/
theorem universallyClosed_structureHom (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    (MorphismProperty.over (@UniversallyClosed)).relative uliftYoneda.{u + 1}
      (structureHomPullback k k' hdeg).hom :=
  sorry

/-- The covering morphism `Spec(k') ⟶ Spec(k)` of a finite Galois extension is
universally closed. -/
instance instUniversallyClosed_groundCover (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] [FiniteDimensional k k'] :
    UniversallyClosed (groundCover k k') := sorry

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
