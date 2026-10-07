module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import stacks_project.Chap65.Example_65_14_2_Presentation

/-!
# The non-representable quadratic quotient

This module records the fppf sheaf quotient `X = U / R` of the quadratic Galois cover by the
étale equivalence relation of `Example_65_14_2_Presentation`, together with the structure
morphism `X → S` and its source-facing properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/-- The fppf sheaf `X = U / R`, obtained by sheafifying the universe-raised quotient presheaf. -/
def sheafOfPoints (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)) :=
  (preRelation k k' hdeg).quotientSheaf (Scheme.fppfTopology.over (base k))

/-- `sheafOfPoints` is the fppf quotient sheaf of the quadratic Galois pre-relation. -/
theorem sheafOfPoints_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    sheafOfPoints k k' hdeg =
      (preRelation k k' hdeg).quotientSheaf (Scheme.fppfTopology.over (base k)) := sorry

/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical quotient map. -/
def atlas (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k k') ⟶
      sheafOfPoints k k' hdeg :=
  (preRelation k k' hdeg).quotientMap (Scheme.fppfTopology.over (base k))

/-- The atlas is the canonical fppf quotient map of the pre-relation. -/
theorem atlas_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    atlas k k' hdeg = (preRelation k k' hdeg).quotientMap (Scheme.fppfTopology.over (base k)) :=
  sorry

/-- The atlas `U ⟶ X` is representable and étale with respect to `uliftYoneda`. -/
theorem atlas_etale (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k k' hdeg).hom :=
  sorry

/-- The atlas `U ⟶ X` is étale-locally surjective. -/
theorem atlas_locallySurjective (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k k' hdeg).hom :=
  sorry

/-- The diagonal of the fppf quotient sheaf `X = U / R` is representable. -/
theorem representableDiagonal_sheafOfPoints (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k k' hdeg).obj) := sorry

/-- The fppf quotient sheaf `X = U / R` is an algebraic space over `S`: it has a representable
étale locally-surjective atlas from `U` and a representable diagonal. -/
theorem sheafOfPoints_spec (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k k' hdeg).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k k' hdeg).hom ∧
        uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k k' hdeg).obj) :=
  sorry

/-- The identity object `S` over `S`. -/
def baseAsOver (k : Type u) [Field k] : Over (base k) := Over.mk (𝟙 (base k))

/-- `baseAsOver` is the identity morphism of `S`, viewed in `Over S`. -/
theorem baseAsOver_eq (k : Type u) [Field k] : baseAsOver k = Over.mk (𝟙 (base k)) := sorry

/-- The unique map `U ⟶ S` in `Over S`. -/
theorem coverToBase_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (cover k k').hom ≫ (baseAsOver k).hom = (cover k k').hom := sorry

/-- The unique map `U ⟶ S` in `Over S`. -/
def coverToBase (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    cover k k' ⟶ baseAsOver k :=
  Over.homMk ((cover k k').hom : (cover k k').left ⟶ (baseAsOver k).left) (coverToBase_w k k')

/-- The underlying scheme morphism of `coverToBase` is the structure map of the cover. -/
theorem coverToBase_left (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (coverToBase k k').left = (cover k k').hom := sorry

/-- Every object of `Over S` has a unique map to `S` over `S`. -/
theorem toBaseAsOver_w (k : Type u) [Field k] (T : Over (base k)) :
    T.hom ≫ (baseAsOver k).hom = T.hom := sorry

/-- The unique map from `T` to `S` over `S`. -/
def toBaseAsOver (k : Type u) [Field k] (T : Over (base k)) : T ⟶ baseAsOver k :=
  Over.homMk (T.hom : T.left ⟶ (baseAsOver k).left) (toBaseAsOver_w k T)

/-- `toBaseAsOver` is classified by the structure morphism of `T`. -/
theorem toBaseAsOver_left (k : Type u) [Field k] (T : Over (base k)) :
    (toBaseAsOver k T).left = T.hom := sorry

/-- The underlying presheaf morphism of `X ⟶ S`. -/
def structureHomVal (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (sheafOfPoints k k' hdeg).obj ⟶
      yoneda.obj (baseAsOver k) ⋙ uliftFunctor.{u + 1} where
  app T :=
    TypeCat.ofHom fun _ : (sheafOfPoints k k' hdeg).obj.obj T ↦
      ULift.up.{u + 1} (toBaseAsOver k (unop T))
  naturality := sorry

/-- The component of `structureHomVal` at `T` is constantly the unique map into `S`. -/
theorem structureHomVal_app (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (T : (Over (base k))ᵒᵖ)
    (x : (sheafOfPoints k k' hdeg).obj.obj T) :
    (structureHomVal k k' hdeg).app T x =
      ULift.up.{u + 1} (toBaseAsOver k (unop T)) := sorry

/-- The structure morphism `X ⟶ S` of fppf sheaves over `S`. -/
def structureHom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    sheafOfPoints k k' hdeg ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (baseAsOver k) :=
  CategoryTheory.ObjectProperty.homMk (structureHomVal k k' hdeg)

/-- The structure morphism sends every section to the unique map into `S` over `S`. -/
theorem structureHom_app (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (T : (Over (base k))ᵒᵖ)
    (x : (sheafOfPoints k k' hdeg).obj.obj T) :
    (structureHom k k' hdeg).hom.app T x = ULift.up.{u + 1} (toBaseAsOver k T.unop) := sorry

/-- `X → S` is an isomorphism over `S \ {0_S}`. -/
theorem isIso_over_punctured (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (T : Over (base k))
    (hT : Set.range (fun x : T.left ↦ T.hom x) ⊆ basePuncturedOpen k) :
    Function.Bijective ((structureHom k k' hdeg).hom.app (Opposite.op T)) := sorry

/-- The morphism `X → S` is étale in the sense of Properties of Spaces, Definition 66.16.2:
postcomposition with `X → S` preserves étale morphisms from schemes, without requiring
`X → S` itself to be representable. -/
theorem etale_structureHom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    ∀ (T : Over (base k))
      (φ : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj T ⟶
        sheafOfPoints k k' hdeg),
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} φ.hom →
        (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
          (φ.hom ≫ (structureHom k k' hdeg).hom) := sorry

/-- The origin of `S`, as an object of `Over S`. -/
def originBaseOver (k : Type u) [Field k] : Over (base k) := Over.mk (originBase k)

/-- `originBaseOver` is the origin morphism `Spec(k) ⟶ S`. -/
theorem originBaseOver_eq (k : Type u) [Field k] :
    originBaseOver k = Over.mk (originBase k) := sorry

/-- The origin of `U` as an object of `Over S`. -/
def originOver (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Over (base k) :=
  Over.mk (originHom k k' ≫ (cover k k').hom)

/-- `originOver` is the composite `Spec(k') ⟶ U ⟶ S`. -/
theorem originOver_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (originOver k k').hom = originHom k k' ≫ (cover k k').hom := sorry

/-- The origin of `S` as a morphism `Spec(k) ⟶ S` over `S`. -/
theorem originToBase_w (k : Type u) [Field k] :
    originBase k ≫ (baseAsOver k).hom = (originBaseOver k).hom := sorry

/-- The origin of `S` as a morphism to `S` in `Over S`. -/
def originToBase (k : Type u) [Field k] : originBaseOver k ⟶ baseAsOver k :=
  Over.homMk (originBase k : (originBaseOver k).left ⟶ (baseAsOver k).left) (originToBase_w k)

/-- The underlying scheme morphism of `originToBase` is `originBase`. -/
theorem originToBase_left (k : Type u) [Field k] :
    (originToBase k).left = originBase k := sorry

/-- The fibre of `X → S` over `0_S` is isomorphic to `Spec(k') = 0_U`. -/
theorem fiber_origin_iso (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Nonempty
      (Limits.pullback (structureHom k k' hdeg)
          ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (originToBase k)) ≅
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (originOver k k')) :=
  sorry

/-- `X` is not representable by a scheme over `S`. -/
theorem not_isRepresentable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    ¬ ∃ T : Over (base k),
        Nonempty
          (sheafOfPoints k k' hdeg ≅
            (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj T) :=
  sorry

/-- If `X` were a scheme, then `𝒪_{X, 0_X}` would be a local domain with fraction field
`k(x)`, with the image of `Polynomial.X` in the maximal ideal, and residue field `k'` as a
`k`-algebra, which is impossible. -/
theorem impossible_origin_localRing (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    ¬ ∃ (𝒪 : Type u) (_ : CommRing 𝒪) (_ : IsDomain 𝒪) (_ : IsLocalRing 𝒪)
        (φ : Polynomial k →+* 𝒪)
        (eFrac : FractionRing 𝒪 ≃+* FractionRing (Polynomial k))
        (eRes : IsLocalRing.ResidueField 𝒪 ≃+* k'),
        Function.Injective φ ∧
          (∀ p : Polynomial k,
            eFrac (algebraMap 𝒪 (FractionRing 𝒪) (φ p)) =
              algebraMap (Polynomial k) (FractionRing (Polynomial k)) p) ∧
            φ Polynomial.X ∈ IsLocalRing.maximalIdeal 𝒪 ∧
              ∀ a : k, eRes (IsLocalRing.residue 𝒪 (φ (Polynomial.C a))) = algebraMap k k' a :=
  sorry

/-- The diagonal of `X` is not a closed immersion, so `X` is not separated over `S`. -/
theorem not_isClosedImmersion_diag (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    ¬ (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k k' hdeg).obj) := sorry

/-- The diagonal of `X` is an immersion, so `X` is locally separated over `S`. -/
theorem isImmersion_diag (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (MorphismProperty.over (@IsImmersion)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k k' hdeg).obj) := sorry

/-- The diagonal of `X` is quasi-compact, so `X` is quasi-separated over `S`. -/
theorem quasiCompact_diag (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k k' hdeg).obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
