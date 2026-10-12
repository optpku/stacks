/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap90.Situation_90_29_1_Pullback
public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap98.Lemma_98_3_3_Predeformation
public import stacks_project.Chap98.Lemma_98_7_1_Residue

/-!
# Change-of-field comparison of predeformation categories

A finite residue-field extension `k → l` induces a canonical 1-morphism of categories
cofibered in groupoids from the Situation 90.29.1 reindexing `(ℱ_{𝒳, k, x₀})_{l/k}` to
`ℱ_{𝒳, l, x_{l,0}}`. Under condition (RS) this 1-morphism is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open ArtinianLocalAlgCat
open scoped BasedFunctor CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (k l : Type u) [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))

/-- The residue-field reindexing of `ℱ_{𝒳, k, x₀}` along `C_{Λ, l} ⥤ C_{Λ, k}`. -/
abbrev residueChangePredeformation :=
  residueChangeOver Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)

/-- `residueChangePredeformation` is the Situation 90.29.1 pullback projection of
`predeformationFunctor`. -/
theorem residueChangePredeformation_eq :
    residueChangePredeformation k l openImmersion kToS h_factor X x0 =
      residueChangeOver Λ k l (predeformationFunctor X openImmersion kToS h_factor x0) :=
  sorry

/-- The morphism `Spec(B) ⟶ Spec(ξ.base)` over `S` obtained by composing
`specOverResidueChange` with `Spec` of the structural isomorphism of a residue-change object. -/
def specOverChangeOfField
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    specOver openImmersion ξ.fst ⟶ specOver openImmersion ξ.snd.base :=
  specOverResidueChange k l openImmersion ξ.fst ≫ specOverMap openImmersion ξ.iso.inv

/-- `specOverChangeOfField` is the composite of `specOverResidueChange` with `specOverMap` of
the inverse structural isomorphism. -/
theorem specOverChangeOfField_spec
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ =
      specOverResidueChange k l openImmersion ξ.fst ≫ specOverMap openImmersion ξ.iso.inv :=
  sorry

/-- Factor an ambient arrow of `𝒳` through the selected cartesian lift of a morphism of `Over S`. -/
def factorOver {U V W : Over S} (f : V ⟶ U) (g : W ⟶ V) (x : X.p.Fiber U) {y}
    (φ : y ⟶ x.1) (hφ : X.p.IsHomLift (g ≫ f) φ) : y ⟶ (Chosen.reindexObj X.p f x).1 :=
  @Chosen.cartesianFactor _ _ _ _ X.p _ U V W f g x y φ hφ

/-- `factorOver` produces an arrow lying over the remaining base morphism `g`. -/
theorem factorOver_isHomLift {U V W : Over S} (f : V ⟶ U) (g : W ⟶ V)
    (x : X.p.Fiber U) {y} (φ : y ⟶ x.1) (hφ : X.p.IsHomLift (g ≫ f) φ) :
    X.p.IsHomLift g (factorOver X f g x φ hφ) :=
  sorry

/-- The object of `ℱ_{𝒳, l, x_{l,0}}` associated to a residue-change object by restricting
along `Spec(B) ⟶ Spec(B ×_l k)`. -/
def changeOfFieldObj
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    Obj openImmersion (lToS k l kToS) (lToS_factor k l openImmersion kToS) X
      (restrictResidue k l kToS X x0) where
  base := ξ.fst
  target := Chosen.reindexObj X.p (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
    ξ.snd.target
  fromResidue :=
    factorOver X (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
      (specOver_toResidue openImmersion (lToS k l kToS) (lToS_factor k l openImmersion kToS) ξ.fst)
      ξ.snd.target (Chosen.cartesianHom X.p (residueOverHom k l kToS) x0 ≫ ξ.snd.fromResidue) sorry
  over_fromResidue := sorry

/-- `changeOfFieldObj` preserves the stored Artinian local algebra `B`. -/
theorem changeOfFieldObj_base
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    (changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ).base = ξ.fst :=
  sorry

/-- The reversed arrow of `ℱ_{𝒳, l, x_{l,0}}` associated to a residue-change morphism, obtained
by cartesian factorization of the reversed `k`-arrow. -/
def changeOfFieldHom
    {ξ η : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)}
    (f : ξ ⟶ η) :
    changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ ⟶
      changeOfFieldObj k l openImmersion kToS h_factor X x0 η where
  baseHom := f.fst
  hom :=
    factorOver X (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
      (specOverMap openImmersion f.fst) ξ.snd.target
      (Chosen.cartesianHom X.p (specOverChangeOfField k l openImmersion kToS h_factor X x0 η)
          η.snd.target ≫
        f.snd.hom) sorry
  over_hom := sorry
  triangle := sorry

/-- `changeOfFieldHom` preserves the underlying morphism of Artinian local algebras. -/
theorem changeOfFieldHom_baseHom
    {ξ η : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)}
    (f : ξ ⟶ η) :
    (changeOfFieldHom k l openImmersion kToS h_factor X x0 f).baseHom = f.fst :=
  sorry

/-- The ordinary functor `(ℱ_{𝒳, k, x₀})_{l/k} ⥤ ℱ_{𝒳, l, x_{l,0}}`. -/
def changeOfFieldToFunctor :
    residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0) ⥤
      Obj openImmersion (lToS k l kToS) (lToS_factor k l openImmersion kToS) X
        (restrictResidue k l kToS X x0) where
  obj ξ := changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ
  map f := changeOfFieldHom k l openImmersion kToS h_factor X x0 f
  map_id := sorry
  map_comp := sorry

/-- The object map of `changeOfFieldToFunctor` is `changeOfFieldObj`. -/
theorem changeOfFieldToFunctor_obj
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    (changeOfFieldToFunctor k l openImmersion kToS h_factor X x0).obj ξ =
      changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ :=
  sorry

/-- The canonical based functor `(ℱ_{𝒳, k, x₀})_{l/k} ⥤ᵇ ℱ_{𝒳, l, x_{l,0}}` over
`ArtinianLocalAlgCat Λ l`. -/
def changeOfField :
    BasedCategory.ofFunctor (residueChangePredeformation k l openImmersion kToS h_factor X x0) ⥤ᵇ
      BasedCategory.ofFunctor
        (predeformationFunctor X openImmersion (lToS k l kToS)
          (lToS_factor k l openImmersion kToS) (restrictResidue k l kToS X x0)) :=
  BasedFunctor.ofFunctor (changeOfFieldToFunctor k l openImmersion kToS h_factor X x0) sorry

/-- `changeOfField` preserves the stored Artinian local algebra `B`. -/
theorem changeOfField_obj_base
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    ((changeOfField k l openImmersion kToS h_factor X x0).obj ξ).base = ξ.fst :=
  sorry

/-- `changeOfField` lies strictly over `C_{Λ, l}`. -/
theorem changeOfField_forget :
    (changeOfField k l openImmersion kToS h_factor X x0).toFunctor ⋙
        predeformationFunctor X openImmersion (lToS k l kToS)
          (lToS_factor k l openImmersion kToS) (restrictResidue k l kToS X x0) =
      residueChangePredeformation k l openImmersion kToS h_factor X x0 :=
  sorry

/-- Objects of `changeOfField` are the cleavage restriction of the `B ×_l k`-data along
`Spec(B) ⟶ Spec(B ×_l k)`. -/
theorem changeOfField_spec
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    ((changeOfField k l openImmersion kToS h_factor X x0).obj ξ).base = ξ.fst ∧
      ((changeOfField k l openImmersion kToS h_factor X x0).obj ξ).target =
        Chosen.reindexObj X.p (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
          ξ.snd.target :=
  sorry

/-- The residue-change reindexing of `ℱ_{𝒳, k, x₀}`, as a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ l`. -/
def residueChangeBundled :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ l) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (residueChangePredeformation k l openImmersion kToS h_factor X x0)

/-- The projection of `residueChangeBundled` is `residueChangePredeformation`. -/
theorem residueChangeBundled_p :
    (residueChangeBundled k l openImmersion kToS h_factor X x0).p =
      residueChangePredeformation k l openImmersion kToS h_factor X x0 :=
  sorry

/-- The canonical 1-morphism `(ℱ_{𝒳, k, x₀})_{l/k} ⟶ ℱ_{𝒳, l, x_{l,0}}` of categories
cofibered in groupoids over `C_{Λ, l}`. -/
def changeOfFieldBundled :
    residueChangeBundled k l openImmersion kToS h_factor X x0 ⟶
      bundled openImmersion (lToS k l kToS) (lToS_factor k l openImmersion kToS) X
        (restrictResidue k l kToS X x0) :=
  CofiberedCategoryOver.Groupoids.ofBasedFunctor (changeOfField k l openImmersion kToS h_factor X x0)

/-- Forgetting `changeOfFieldBundled` to based functors recovers `changeOfField`. -/
theorem changeOfFieldBundled_toBasedFunctor :
    CofiberedCategoryOver.Groupoids.toBasedFunctor
        (changeOfFieldBundled k l openImmersion kToS h_factor X x0) =
      changeOfField k l openImmersion kToS h_factor X x0 :=
  sorry

/-- Under condition (RS), the change-of-field 1-morphism is an equivalence over `C_{Λ, l}`. -/
instance instIsEquivalence_changeOfField [HasRimSchlessinger X] :
    BasedFunctor.IsEquivalence
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (changeOfFieldBundled k l openImmersion kToS h_factor X x0)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
