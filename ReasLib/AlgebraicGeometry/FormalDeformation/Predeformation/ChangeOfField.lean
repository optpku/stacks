/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Cofibered
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Bundled
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.ResidueExtension

/-!
# Change-of-field comparison of predeformation categories

A finite residue-field extension `k → l` induces a canonical 1-morphism of categories
cofibered in groupoids from the residue-field reindexing `(ℱ_{𝒳, k, x₀})_{l/k}` to
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

/-- A residue-compatible local algebra map commutes with the identified residue maps. -/
theorem toResidueHom_naturality {A B : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ B) (a : A.carrier) : toResidueHom B (f.hom a) = toResidueHom A a := by
  change B.residueFieldIso (IsLocalRing.residue _ (f.hom a)) =
    A.residueFieldIso (IsLocalRing.residue _ a)
  have h := DFunLike.congr_fun (ArtinianLocalAlgCat.Hom.residue_compat f)
    (IsLocalRing.residue A.carrier a)
  simpa [residueCompat, residueMap, residueIsoHom] using h

/-- The spectrum maps over `S` reverse composition of Artinian local algebra maps. -/
theorem specOverMap_map_comp {A B C : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ B) (g : B ⟶ C) :
    specOverMap openImmersion (f ≫ g) =
      specOverMap openImmersion g ≫ specOverMap openImmersion f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.hom.toRingHom ≫ CommRingCat.ofHom g.hom.toRingHom) = _
  exact Spec.map_comp _ _

/-- The residue spectrum maps are natural in the Artinian local algebra. -/
theorem specOver_toResidue_naturality {A B : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ B) :
    specOver_toResidue openImmersion kToS h_factor B ≫ specOverMap openImmersion f =
      specOver_toResidue openImmersion kToS h_factor A := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact toResidueHom_naturality k f a

/-- The spectrum of the first residue-change projection is natural in the algebra. -/
theorem specOverResidueChange_naturality {B B' : ArtinianLocalAlgCat Λ l}
    (f : B ⟶ B') :
    specOverMap openImmersion f ≫ specOverResidueChange k l openImmersion B =
      specOverResidueChange k l openImmersion B' ≫
        specOverMap openImmersion (residueChangeMap k f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

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
  rfl

/-- The change-of-field spectrum map commutes with the two residue spectrum maps. -/
theorem specOverChangeOfField_residue
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    specOver_toResidue openImmersion (lToS k l kToS)
        (lToS_factor k l openImmersion kToS h_factor) ξ.fst ≫
      specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ =
    residueOverHom k l kToS ≫ specOver_toResidue openImmersion kToS h_factor ξ.snd.base := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  change toResidueHom ξ.fst (residueChangeFst k ξ.fst (ξ.iso.inv.hom a)) =
    algebraMap k l (toResidueHom ξ.snd.base a)
  calc
    _ = algebraMap k l (ξ.iso.inv.hom a).val.2 := (ξ.iso.inv.hom a).property
    _ = algebraMap k l (toResidueHom (residueChange k ξ.fst) (ξ.iso.inv.hom a)) :=
      congrArg (algebraMap k l) (residueChangeResidueFieldIso_residue k ξ.fst _).symm
    _ = _ := congrArg (algebraMap k l) (toResidueHom_naturality k ξ.iso.inv a)

/-- The change-of-field spectrum maps commute with the two components of a pullback arrow. -/
theorem specOverChangeOfField_naturality
    {ξ η : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)}
    (f : ξ ⟶ η) :
    specOverMap openImmersion f.fst ≫ specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ =
      specOverChangeOfField k l openImmersion kToS h_factor X x0 η ≫
        specOverMap openImmersion f.snd.baseHom := by
  have hw := congrArg (specOverMap openImmersion) (CategoricalPullback.Hom.w' f)
  change specOverMap openImmersion (f.snd.baseHom ≫ η.iso.inv) =
    specOverMap openImmersion (ξ.iso.inv ≫ residueChangeMap k f.fst) at hw
  simp only [specOverMap_map_comp] at hw
  dsimp only [specOverChangeOfField]
  rw [← Category.assoc, specOverResidueChange_naturality, Category.assoc]
  exact (congrArg (fun q => specOverResidueChange k l openImmersion η.fst ≫ q) hw.symm).trans
    (Category.assoc _ _ _).symm

-- Permit this private implementation adapter in the two public construction bodies below.
set_option backward.privateInPublic true in
/-- Factor an ambient arrow of `𝒳` through the selected cartesian lift of a morphism of `Over S`. -/
private def factorOver {U V W : Over S} (f : V ⟶ U) (g : W ⟶ V) (x : X.p.Fiber U) {y}
    (φ : y ⟶ x.1) (hφ : X.p.IsHomLift (g ≫ f) φ) : y ⟶ (Chosen.reindexObj X.p f x).1 :=
  @Chosen.cartesianFactor _ _ _ _ X.p _ U V W f g x y φ hφ

-- The concrete object construction uses the private explicit-proof adapter only internally.
set_option backward.privateInPublic true in
/-- The object of `ℱ_{𝒳, l, x_{l,0}}` associated to a residue-change object by restricting
along `Spec(B) ⟶ Spec(B ×_l k)`. -/
def changeOfFieldObj
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    Obj openImmersion (lToS k l kToS) (lToS_factor k l openImmersion kToS h_factor) X
      (restrictResidue k l kToS X x0) := by
  have compatibility : X.p.IsHomLift
      (specOver_toResidue openImmersion (lToS k l kToS)
        (lToS_factor k l openImmersion kToS h_factor) ξ.fst ≫
          specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
      (Chosen.cartesianHom X.p (residueOverHom k l kToS) x0 ≫ ξ.snd.fromResidue) := by
    rw [specOverChangeOfField_residue]
    exact @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ _ _ _ _
      (Chosen.cartesianHom.isHomLift X.p (residueOverHom k l kToS) x0)
      ξ.snd.over_fromResidue
  exact
    { base := ξ.fst
      target := Chosen.reindexObj X.p
        (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ) ξ.snd.target
      fromResidue := factorOver X
        (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
        (specOver_toResidue openImmersion (lToS k l kToS)
          (lToS_factor k l openImmersion kToS h_factor) ξ.fst)
        ξ.snd.target
        (Chosen.cartesianHom X.p (residueOverHom k l kToS) x0 ≫ ξ.snd.fromResidue)
        compatibility
      over_fromResidue := @Chosen.cartesianFactor.isHomLift _ _ _ _ X.p _ _ _ _ _ _ _ _ _
        compatibility }

/-- `changeOfFieldObj` preserves the stored Artinian local algebra `B`. -/
theorem changeOfFieldObj_base
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    (changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ).base = ξ.fst :=
  rfl

/-- The new residue arrow factors the original residue arrow through the selected cartesian lift. -/
theorem changeOfFieldObj_fac
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    (changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ).fromResidue ≫
        Chosen.cartesianHom X.p
          (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ) ξ.snd.target =
      Chosen.cartesianHom X.p (residueOverHom k l kToS) x0 ≫ ξ.snd.fromResidue := by
  have compatibility : X.p.IsHomLift
      (specOver_toResidue openImmersion (lToS k l kToS)
        (lToS_factor k l openImmersion kToS h_factor) ξ.fst ≫
          specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
      (Chosen.cartesianHom X.p (residueOverHom k l kToS) x0 ≫ ξ.snd.fromResidue) := by
    rw [specOverChangeOfField_residue]
    exact @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ _ _ _ _
      (Chosen.cartesianHom.isHomLift X.p (residueOverHom k l kToS) x0)
      ξ.snd.over_fromResidue
  exact @Chosen.cartesianFactor.fac _ _ _ _ X.p _ _ _ _ _ _ _ _ _ compatibility

-- The concrete arrow construction uses the same private adapter without exposing its binders.
set_option backward.privateInPublic true in
/-- The reversed arrow of `ℱ_{𝒳, l, x_{l,0}}` associated to a residue-change morphism, obtained
by cartesian factorization of the reversed `k`-arrow. -/
def changeOfFieldHom
    {ξ η : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)}
    (f : ξ ⟶ η) :
    changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ ⟶
      changeOfFieldObj k l openImmersion kToS h_factor X x0 η := by
  let φ := Chosen.cartesianHom X.p
    (specOverChangeOfField k l openImmersion kToS h_factor X x0 η) η.snd.target ≫ f.snd.hom
  have compatibility :
      X.p.IsHomLift (specOverMap openImmersion f.fst ≫
        specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ) φ ∧
      (∀ hφ : X.p.IsHomLift (specOverMap openImmersion f.fst ≫
          specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ) φ,
        (changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ).fromResidue =
          (changeOfFieldObj k l openImmersion kToS h_factor X x0 η).fromResidue ≫
            factorOver X (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
              (specOverMap openImmersion f.fst) ξ.snd.target φ hφ) := by
    constructor
    · rw [specOverChangeOfField_naturality]
      exact @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ _ _ _ _
        (Chosen.cartesianHom.isHomLift X.p
          (specOverChangeOfField k l openImmersion kToS h_factor X x0 η) η.snd.target)
        f.snd.over_hom
    · intro hφ
      have hfactor := @Chosen.cartesianFactor.isHomLift _ _ _ _ X.p _ _ _ _
        (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
        (specOverMap openImmersion f.fst) ξ.snd.target _ φ hφ
      have hcomp := @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ _ _ _ _
        (changeOfFieldObj k l openImmersion kToS h_factor X x0 η).over_fromResidue hfactor
      have hright : X.p.IsHomLift
          (specOver_toResidue openImmersion (lToS k l kToS)
            (lToS_factor k l openImmersion kToS h_factor) ξ.fst)
          ((changeOfFieldObj k l openImmersion kToS h_factor X x0 η).fromResidue ≫
            factorOver X (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
              (specOverMap openImmersion f.fst) ξ.snd.target φ hφ) :=
        (specOver_toResidue_naturality l openImmersion (lToS k l kToS)
          (lToS_factor k l openImmersion kToS h_factor) f.fst) ▸ hcomp
      apply @Chosen.cartesianHom.ambient_ext _ _ _ _ X.p _ _ _ _
        (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
        (specOver_toResidue openImmersion (lToS k l kToS)
          (lToS_factor k l openImmersion kToS h_factor) ξ.fst)
        ξ.snd.target _ _ _
        (changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ).over_fromResidue hright
      dsimp only [factorOver]
      rw [Category.assoc, Chosen.cartesianFactor.fac]
      have hξ := changeOfFieldObj_fac k l openImmersion kToS h_factor X x0 ξ
      have hη := changeOfFieldObj_fac k l openImmersion kToS h_factor X x0 η
      have htriangle := congrArg
        (Chosen.cartesianHom X.p (residueOverHom k l kToS) x0 ≫ ·) f.snd.triangle
      exact hξ.trans (htriangle.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f.snd.hom) hη.symm).trans (Category.assoc _ _ _))))
  exact
    { baseHom := f.fst
      hom := factorOver X (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
        (specOverMap openImmersion f.fst) ξ.snd.target φ compatibility.1
      over_hom := @Chosen.cartesianFactor.isHomLift _ _ _ _ X.p _ _ _ _ _ _ _ _ _
        compatibility.1
      triangle := compatibility.2 compatibility.1 }

/-- `changeOfFieldHom` preserves the underlying morphism of Artinian local algebras. -/
theorem changeOfFieldHom_baseHom
    {ξ η : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)}
    (f : ξ ⟶ η) :
    (changeOfFieldHom k l openImmersion kToS h_factor X x0 f).baseHom = f.fst :=
  rfl

/-- The new reversed arrow factors the original reversed arrow through the cartesian lift. -/
theorem changeOfFieldHom_fac
    {ξ η : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)}
    (f : ξ ⟶ η) :
    (changeOfFieldHom k l openImmersion kToS h_factor X x0 f).hom ≫
        Chosen.cartesianHom X.p
          (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ) ξ.snd.target =
      Chosen.cartesianHom X.p
        (specOverChangeOfField k l openImmersion kToS h_factor X x0 η) η.snd.target ≫
          f.snd.hom := by
  have compatibility : X.p.IsHomLift
      (specOverMap openImmersion f.fst ≫
        specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
      (Chosen.cartesianHom X.p
        (specOverChangeOfField k l openImmersion kToS h_factor X x0 η) η.snd.target ≫
          f.snd.hom) := by
    rw [specOverChangeOfField_naturality]
    exact @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ _ _ _ _
      (Chosen.cartesianHom.isHomLift X.p
        (specOverChangeOfField k l openImmersion kToS h_factor X x0 η) η.snd.target)
      f.snd.over_hom
  exact @Chosen.cartesianFactor.fac _ _ _ _ X.p _ _ _ _ _ _ _ _ _ compatibility

/-- A predeformation arrow is determined by its algebra map and reversed ambient arrow. -/
theorem Hom.ext_baseHom_hom {ξ η : Obj openImmersion kToS h_factor X x0}
    {f g : ξ ⟶ η} (hbase : f.baseHom = g.baseHom) (hhom : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases hbase
  cases hhom
  rfl

/-- The ordinary functor `(ℱ_{𝒳, k, x₀})_{l/k} ⥤ ℱ_{𝒳, l, x_{l,0}}`. -/
def changeOfFieldToFunctor :
    residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0) ⥤
      Obj openImmersion (lToS k l kToS) (lToS_factor k l openImmersion kToS h_factor) X
        (restrictResidue k l kToS X x0) := by
  have laws :
      (∀ ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0),
        changeOfFieldHom k l openImmersion kToS h_factor X x0 (𝟙 ξ) =
          𝟙 (changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ)) ∧
      (∀ (ξ η ζ : residueChangeTotal Λ k l
          (predeformationFunctor X openImmersion kToS h_factor x0)) (f : ξ ⟶ η) (g : η ⟶ ζ),
        changeOfFieldHom k l openImmersion kToS h_factor X x0 (f ≫ g) =
          changeOfFieldHom k l openImmersion kToS h_factor X x0 f ≫
            changeOfFieldHom k l openImmersion kToS h_factor X x0 g) := by
    constructor
    · intro ξ
      apply Hom.ext_baseHom_hom
      · rfl
      · apply @Chosen.cartesianHom.ambient_ext _ _ _ _ X.p _ _ _ _
          (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
          (specOverMap openImmersion (𝟙 ξ.fst)) ξ.snd.target _ _ _
          (changeOfFieldHom k l openImmersion kToS h_factor X x0 (𝟙 ξ)).over_hom
          (Hom.over_hom (𝟙 (changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ)))
        exact (changeOfFieldHom_fac k l openImmersion kToS h_factor X x0 (𝟙 ξ)).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm)
    · intro ξ η ζ f g
      apply Hom.ext_baseHom_hom
      · rfl
      · apply @Chosen.cartesianHom.ambient_ext _ _ _ _ X.p _ _ _ _
          (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
          (specOverMap openImmersion (f.fst ≫ g.fst)) ξ.snd.target _ _ _
          (changeOfFieldHom k l openImmersion kToS h_factor X x0 (f ≫ g)).over_hom
          (Hom.over_hom (changeOfFieldHom k l openImmersion kToS h_factor X x0 f ≫
            changeOfFieldHom k l openImmersion kToS h_factor X x0 g))
        have hf := changeOfFieldHom_fac k l openImmersion kToS h_factor X x0 f
        have hg := changeOfFieldHom_fac k l openImmersion kToS h_factor X x0 g
        have hfg := changeOfFieldHom_fac k l openImmersion kToS h_factor X x0 (f ≫ g)
        exact hfg.trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ f.snd.hom) hg.symm).trans ((Category.assoc _ _ _).trans
            ((congrArg ((changeOfFieldHom k l openImmersion kToS h_factor X x0 g).hom ≫ ·)
              hf.symm).trans (Category.assoc _ _ _).symm))))
  exact
    { obj ξ := changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ
      map f := changeOfFieldHom k l openImmersion kToS h_factor X x0 f
      map_id := laws.1
      map_comp := fun f g => laws.2 _ _ _ f g }

/-- The object map of `changeOfFieldToFunctor` is `changeOfFieldObj`. -/
theorem changeOfFieldToFunctor_obj
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    (changeOfFieldToFunctor k l openImmersion kToS h_factor X x0).obj ξ =
      changeOfFieldObj k l openImmersion kToS h_factor X x0 ξ :=
  rfl

/-- The canonical based functor `(ℱ_{𝒳, k, x₀})_{l/k} ⥤ᵇ ℱ_{𝒳, l, x_{l,0}}` over
`ArtinianLocalAlgCat Λ l`. -/
def changeOfField :
    BasedCategory.ofFunctor (residueChangeOver Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) ⥤ᵇ
      BasedCategory.ofFunctor
        (predeformationFunctor X openImmersion (lToS k l kToS)
          (lToS_factor k l openImmersion kToS h_factor) (restrictResidue k l kToS X x0)) :=
  BasedFunctor.ofFunctor (changeOfFieldToFunctor k l openImmersion kToS h_factor X x0) rfl

/-- `changeOfField` preserves the stored Artinian local algebra `B`. -/
theorem changeOfField_obj_base
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    ((changeOfField k l openImmersion kToS h_factor X x0).obj ξ).base = ξ.fst :=
  rfl

/-- `changeOfField` lies strictly over `C_{Λ, l}`. -/
theorem changeOfField_forget :
    (changeOfField k l openImmersion kToS h_factor X x0).toFunctor ⋙
        predeformationFunctor X openImmersion (lToS k l kToS)
          (lToS_factor k l openImmersion kToS h_factor) (restrictResidue k l kToS X x0) =
      residueChangeOver Λ k l (predeformationFunctor X openImmersion kToS h_factor x0) :=
  rfl

/-- Objects of `changeOfField` are the cleavage restriction of the `B ×_l k`-data along
`Spec(B) ⟶ Spec(B ×_l k)`. -/
theorem changeOfField_spec
    (ξ : residueChangeTotal Λ k l (predeformationFunctor X openImmersion kToS h_factor x0)) :
    ((changeOfField k l openImmersion kToS h_factor X x0).obj ξ).base = ξ.fst ∧
      ((changeOfField k l openImmersion kToS h_factor X x0).obj ξ).target =
        Chosen.reindexObj X.p (specOverChangeOfField k l openImmersion kToS h_factor X x0 ξ)
          ξ.snd.target := by
  exact ⟨rfl, rfl⟩

/-- The residue-change reindexing of `ℱ_{𝒳, k, x₀}`, as a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ l`. -/
def residueChangeBundled :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ l) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (residueChangeOver Λ k l (predeformationFunctor X openImmersion kToS h_factor x0))

/-- The projection of the bundled residue-change category is the canonical pullback projection. -/
theorem residueChangeBundled_p :
    (residueChangeBundled k l openImmersion kToS h_factor X x0).p =
      residueChangeOver Λ k l (predeformationFunctor X openImmersion kToS h_factor x0) :=
  rfl

/-- The canonical change-of-field morphism of categories cofibered in groupoids. -/
def changeOfFieldFunctor :
    residueChangeBundled k l openImmersion kToS h_factor X x0 ⟶
      bundled openImmersion (lToS k l kToS) (lToS_factor k l openImmersion kToS h_factor) X
        (restrictResidue k l kToS X x0) :=
  CofiberedCategoryOver.Groupoids.ofBasedFunctor
    (changeOfField k l openImmersion kToS h_factor X x0)

/-- Forgetting `changeOfFieldFunctor` to based functors recovers `changeOfField`. -/
theorem changeOfFieldFunctor_toBasedFunctor :
    CofiberedCategoryOver.Groupoids.toBasedFunctor
        (changeOfFieldFunctor k l openImmersion kToS h_factor X x0) =
      changeOfField k l openImmersion kToS h_factor X x0 :=
  rfl

/-- If `𝒳` satisfies (RS), then the canonical change-of-field functor is
an equivalence of categories cofibered in groupoids over `C_{Λ, l}`. -/
instance changeOfField_isEquivalence [HasRimSchlessinger X] :
    BasedFunctor.IsEquivalence
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (changeOfFieldFunctor k l openImmersion kToS h_factor X x0)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
