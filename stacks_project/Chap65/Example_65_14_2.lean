/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DescentData
open AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

universe u

/- Example 65.14.2. The quadratic Galois quotient yields a non-effective descent datum
for schemes along the covering of the ground field. -/
@[stacks 03FN] #check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.not_isEffective_descentData :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    ¬ (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.descentData k k' hdeg).IsEffective)

/- The quadratic cover and the diagonal together with the punctured Galois graph. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.relationHom :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    relationOver k k' ⟶ cover k k' ⨯ cover k k')

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.isIso_coprod_desc_diagonal_graph :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    IsIso (coprod.desc (diagonalHom k k') (graphHom k k' hdeg)))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.coe_puncturedOpen :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'],
    (puncturedOpen k k' : Set (cover k k').left) = {origin k k'}ᶜ)

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.instIsEtaleEquivalenceRelation_preRelation :
    ∀ (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    (preRelation k k' hdeg).IsEtaleEquivalenceRelation)

/- The quotient sheaf and its étale locally surjective atlas with representable diagonal. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.sheafOfPoints :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.atlas :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k k') ⟶
      sheafOfPoints k k' hdeg)

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.sheafOfPoints_spec :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k k' hdeg).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k k' hdeg).hom ∧
        uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k k' hdeg).obj))

/- The quotient is isomorphic to the base away from the origin. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.isIso_over_punctured :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (T : Over (base k))
    (hT : Set.range (fun x : T.left ↦ T.hom x) ⊆ basePuncturedOpen k),
    Function.Bijective ((structureHom k k' hdeg).hom.app (Opposite.op T)))

/- The structure morphism is étale. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.etale_structureHom :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    ∀ (T : Over (base k))
      (φ : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj T ⟶
        sheafOfPoints k k' hdeg),
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} φ.hom →
        (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
          (φ.hom ≫ (structureHom k k' hdeg).hom))

/- The origin fibre is the spectrum of the quadratic extension. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.fiber_origin_iso :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    Nonempty
      (Limits.pullback (structureHom k k' hdeg)
          ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (originToBase k)) ≅
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (originOver k k')))

/- The quotient is not a scheme, with the specified local-domain obstruction. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.not_isRepresentable :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    ¬ ∃ T : Over (base k),
        Nonempty
          (sheafOfPoints k k' hdeg ≅
            (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj T))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.impossible_origin_localRing :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    ¬ ∃ (𝒪 : Type u) (_ : CommRing 𝒪) (_ : IsDomain 𝒪) (_ : IsLocalRing 𝒪)
        (φ : Polynomial k →+* 𝒪)
        (eFrac : FractionRing 𝒪 ≃+* FractionRing (Polynomial k))
        (eRes : IsLocalRing.ResidueField 𝒪 ≃+* k'),
        Function.Injective φ ∧
          (∀ p : Polynomial k,
            eFrac (algebraMap 𝒪 (FractionRing 𝒪) (φ p)) =
              algebraMap (Polynomial k) (FractionRing (Polynomial k)) p) ∧
            φ Polynomial.X ∈ IsLocalRing.maximalIdeal 𝒪 ∧
              ∀ a : k, eRes (IsLocalRing.residue 𝒪 (φ (Polynomial.C a))) = algebraMap k k' a)

/- The quotient is nonseparated, locally separated, and quasi-separated. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.not_isClosedImmersion_diag :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    ¬ (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k k' hdeg).obj))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.isImmersion_diag :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    (MorphismProperty.over (@IsImmersion)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k k' hdeg).obj))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.quasiCompact_diag :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k k' hdeg).obj))

/- The finite étale surjective cover makes the quotient the line with doubled origin. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.etale_cover_hom :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    Etale (cover k k').hom)

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.isFinite_cover_hom :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    IsFinite (cover k k').hom)

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.surjective_cover_hom :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    Surjective (cover k k').hom)

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.iso_doubledOrigin :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    Nonempty
      (baseChangeSheaf k k' hdeg ≅
        (Scheme.fppfTopology.over (cover k k').left).uliftYoneda.{u + 1}.obj
          (doubledOriginOver k k')))

/- Over the ground field the quotient has a finite-type atlas and becomes a scheme after scalar extension. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.finiteType_overGround :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    LocallyOfFiniteType ((cover k k').hom ≫ toGround k) ∧
      QuasiCompact ((cover k k').hom ≫ toGround k))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.scalarExtension_isRepresentable :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    ∃ T : Over (Spec (CommRingCat.of k')),
      Nonempty
        (scalarExtensionSheaf k k' hdeg ≅
          (Scheme.fppfTopology.over (Spec (CommRingCat.of k'))).uliftYoneda.{u + 1}.obj T))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.not_isRepresentable_overGround :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    ¬ ∃ T : Over (ground k),
        Nonempty
          (sheafOverGround k k' hdeg ≅
            (Scheme.fppfTopology.over (ground k)).uliftYoneda.{u + 1}.obj T))

/- The explicit doubled-origin descent datum and its finite étale surjective ground cover. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.descentObject :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'],
    Over (Spec (CommRingCat.of k')))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.descentData :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    DescentData (fun _ : PUnit.{1} ↦ Spec (CommRingCat.of k')) (fun _ ↦ groundCover k k'))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.etale_groundCover :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    Etale (groundCover k k'))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.isFinite_groundCover :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    IsFinite (groundCover k k'))

#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.surjective_groundCover :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2),
    Surjective (groundCover k k'))
