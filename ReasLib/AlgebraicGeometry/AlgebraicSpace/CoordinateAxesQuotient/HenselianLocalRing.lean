/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient.Space

/-!
# Henselian local ring of the coordinate-axes quotient

Elementary pointed étale charts describe the local ring at the origin of the quotient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient

/-- The stalk of `U` at the origin `0_U`. -/
abbrev originStalk (k : Type u) [Field k] : Type u :=
  (cover k).left.presheaf.stalk (originPoint k)


/-- The stalk of `U` at the origin is a local ring. -/
instance instIsLocalRing_originStalk (k : Type u) [Field k] : IsLocalRing (originStalk k) :=
  inferInstance

/-- The residue-field scheme `Spec(κ(u))` of a point of a scheme over `Spec k`. -/
def residueOver {k : Type u} [Field k] (U : Over (base k)) (u : U.left) : Over (base k) :=
  Over.mk (U.left.fromSpecResidueField u ≫ U.hom)

/-- The structure morphism of `residueOver U u` is `fromSpecResidueField` followed by `U.hom`. -/
theorem residueOver_hom {k : Type u} [Field k] (U : Over (base k)) (u : U.left) :
    (residueOver U u).hom = U.left.fromSpecResidueField u ≫ U.hom := rfl


/-- The residue-field morphism `Spec(κ(u)) ⟶ U` over `Spec k`. -/
def residueι {k : Type u} [Field k] (U : Over (base k)) (u : U.left) :
    residueOver U u ⟶ U :=
  Over.homMk (U.left.fromSpecResidueField u)

/-- The underlying scheme morphism of `residueι` is `fromSpecResidueField`. -/
theorem residueι_left {k : Type u} [Field k] (U : Over (base k)) (u : U.left) :
    (residueι U u).left = U.left.fromSpecResidueField u := rfl

/-- The origin of `𝔸¹_k` is irreducible, as it is `Spec k`. -/
instance instIrreducibleSpace_affineLineOriginOver (k : Type u) [Field k] :
    IrreducibleSpace (affineLineOriginOver k).left := inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of k)))

/-- An elementary étale neighbourhood of the unique point of `sheafOfPoints k`
lying over `0 ∈ 𝔸¹_k`. The selected residue-field morphism is a monomorphism into the quotient. -/
structure ElementaryEtaleNeighborhoodAtOrigin (k : Type u) [Field k] where
  /-- The source scheme of the neighbourhood, as an object over `Spec k`. -/
  obj : Over (base k)
  /-- The étale chart morphism into `sheafOfPoints k`. -/
  hom : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj obj ⟶ sheafOfPoints k
  /-- The chart is étale relative to `uliftYoneda`. -/
  isEtale : (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} hom.hom
  /-- The composite of the chart with `toAffineLine`. -/
  toAffine : obj ⟶ affineLine k
  /-- `toAffine` is the chart composed with `X ⟶ 𝔸¹_k`. -/
  toAffine_fac :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map toAffine = hom ≫ toAffineLine k
  /-- The selected point of the neighbourhood. -/
  point : obj.left
  /-- The selected point lies over the origin of `𝔸¹_k`. -/
  mapsToOrigin :
    toAffine.left point =
      (affineLineOriginToAffineLine k).left.base
        (genericPoint (affineLineOriginOver k).left)
  /-- The neighbourhood is elementary: `Spec(κ(point)) ⟶ X` is a monomorphism. -/
  isElementary :
    Mono
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (residueι obj point) ≫ hom)

/-- The sum map sends the nodal origin to the origin of the affine line. -/
theorem sumOver_originPoint (k : Type u) [Field k] :
    (sumOver k).left (originPoint k) =
      (affineLineOriginToAffineLine k).left.base
        (genericPoint (affineLineOriginOver k).left) := sorry

/-- The residue-field morphism at the nodal origin is monic in the quotient sheaf. -/
theorem mono_residueι_origin_atlas (k : Type u) [Field k] :
    Mono ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
      (residueι (cover k) (originPoint k)) ≫ atlas k) := sorry

/-- The atlas `U ⟶ X` with the origin `0_U` is an elementary étale neighbourhood of
the unique point of `X` over `0`. -/
def ElementaryEtaleNeighborhoodAtOrigin.ofAtlas (k : Type u) [Field k] :
    ElementaryEtaleNeighborhoodAtOrigin k where
  obj := cover k
  hom := atlas k
  isEtale := (sheafOfPoints_spec k).1
  toAffine := sumOver k
  toAffine_fac := (toAffineLine_comp_atlas k).symm
  point := originPoint k
  mapsToOrigin := sumOver_originPoint k
  isElementary := mono_residueι_origin_atlas k

/-- `ofAtlas` is the atlas chart `U ⟶ X` based at `0_U`. -/
theorem ElementaryEtaleNeighborhoodAtOrigin.ofAtlas_spec (k : Type u) [Field k] :
    (ofAtlas k).obj = cover k ∧
      (ofAtlas k).hom = atlas k ∧
        (ofAtlas k).toAffine = sumOver k ∧
          (ofAtlas k).point = originPoint k :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Compatibility of a family of global-section maps with morphisms of elementary
étale neighbourhoods of the unique point over `0`. Transitions must commute with
the charts and send the selected point to the selected point. -/
def ElementaryEtaleNeighborhoodAtOrigin.IsCompatible {k : Type u} [Field k]
    {Ah : Type u} [CommRing Ah]
    (ι : ∀ U : ElementaryEtaleNeighborhoodAtOrigin k, Γ(U.obj.left, ⊤) →+* Ah) : Prop :=
  ∀ {U V : ElementaryEtaleNeighborhoodAtOrigin k} (f : U.obj ⟶ V.obj),
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map f ≫ V.hom = U.hom →
      f.left.base U.point = V.point →
        (ι U).comp (Scheme.Γ.map f.left.op).hom = ι V


/-- `Ah` is the henselian local ring of `sheafOfPoints k` at the unique closed point
over `0`, as the colimit of global-section rings of elementary étale neighbourhoods
of that point. -/
@[mk_iff]
class IsHenselianLocalRingAtOrigin (k : Type u) [Field k] (Ah : Type u) [CommRing Ah] :
    Prop where
  /-- `Ah` is the colimit of `Γ(U, 𝒪_U)` over elementary étale neighbourhoods of
  the unique point of `X` over `0`. -/
  isColimitOfElementaryEtaleNeighborhoods :
    ∃ ι : ∀ U : ElementaryEtaleNeighborhoodAtOrigin k, Γ(U.obj.left, ⊤) →+* Ah,
      ElementaryEtaleNeighborhoodAtOrigin.IsCompatible ι ∧
        ∀ (Bh : Type u) [CommRing Bh]
          (τ : ∀ U : ElementaryEtaleNeighborhoodAtOrigin k, Γ(U.obj.left, ⊤) →+* Bh),
          ElementaryEtaleNeighborhoodAtOrigin.IsCompatible τ →
            ∃! Φ : Ah →+* Bh, ∀ U, Φ.comp (ι U) = τ U

/-- The defining colimit property of `IsHenselianLocalRingAtOrigin`. -/
theorem IsHenselianLocalRingAtOrigin.spec (k : Type u) [Field k]
    (Ah : Type u) [CommRing Ah] [IsHenselianLocalRingAtOrigin k Ah] :
    ∃ ι : ∀ U : ElementaryEtaleNeighborhoodAtOrigin k, Γ(U.obj.left, ⊤) →+* Ah,
      ElementaryEtaleNeighborhoodAtOrigin.IsCompatible ι ∧
        ∀ (Bh : Type u) [CommRing Bh]
          (τ : ∀ U : ElementaryEtaleNeighborhoodAtOrigin k, Γ(U.obj.left, ⊤) →+* Bh),
          ElementaryEtaleNeighborhoodAtOrigin.IsCompatible τ →
            ∃! Φ : Ah →+* Bh, ∀ U, Φ.comp (ι U) = τ U :=
  IsHenselianLocalRingAtOrigin.isColimitOfElementaryEtaleNeighborhoods


/-- A henselization of `originStalk k` realises `IsHenselianLocalRingAtOrigin`. -/
instance instIsHenselianLocalRingAtOrigin_of_isHenselizationOf
    (k : Type u) [Field k]
    (Ah : Type u) [CommRing Ah] [Algebra (originStalk k) Ah]
    [IsHenselizationOf (originStalk k) Ah] :
    IsHenselianLocalRingAtOrigin k Ah := sorry

/-- A henselization of `originStalk k` is not a domain. -/
theorem not_isDomain_of_isHenselizationOf_originStalk
    (k : Type u) [Field k]
    (Ah : Type u) [CommRing Ah] [Algebra (originStalk k) Ah]
    [IsHenselizationOf (originStalk k) Ah] :
    ¬ IsDomain Ah := sorry

end AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient
