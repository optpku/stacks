/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Single
public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.RestrictScalars.Map
public import stacks_project.Chap98.Definition_98_23_5_AffineOpen
public import stacks_project.Chap98.Lemma_98_21_2_Functor
public import stacks_project.Chap98.Lemma_98_23_2_Comparison
public import stacks_project.Chap98.Remark_98_21_3_Functoriality_Map
public import stacks_project.Chap98.Remark_98_21_8_Canonical_element_Lift

/-!
# Naive obstruction theories

On a locally Noetherian base, extra data on a category fibred in groupoids
satisfying (RS*): complexes `E_x` in `D⁻(A)`, maps `ξ_x : E_x ⟶ NL{A⁄Λ}`,
identifications of `Inf_x` and `T_x` with `Ext^{-1}` and `Ext^0`, and
functoriality maps in `D(A)`, subject to the conditions of Definition 98.23.5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open Algebra
open Algebra.Generators
open Algebra.Extension
open DerivedCategory
open HomologicalComplex
open ComplexShape
open scoped NaiveCotangent

noncomputable section

universe u

namespace Algebra.NaiveCotangent

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The self-presentation augmentation `d ≫ toKaehler` vanishes. -/
theorem toKaehler_comp_d :
    (Algebra.naiveCotangent Λ A).d 1 0 ≫
      ModuleCat.ofHom (Generators.self Λ A).toExtension.toKaehler = 0 :=
  sorry

/-- The augmentation `NL{A⁄Λ} ⟶ Ω[A⁄Λ][0]` in the derived category, induced by
the `toKaehler` map of the self-presentation. -/
def naiveCotangentToKaehler :
    Algebra.naiveCotangentObject Λ A ⟶
      (singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A Ω[A⁄Λ]) :=
  DerivedCategory.Q.map
    (extendMap
        ((ChainComplex.toSingle₀Equiv (Algebra.naiveCotangent Λ A)
            (ModuleCat.of A Ω[A⁄Λ])).symm
          ⟨ModuleCat.ofHom (Generators.self Λ A).toExtension.toKaehler,
            toKaehler_comp_d⟩)
        embeddingDownNat ≫
      (extendSingleIso embeddingDownNat (ModuleCat.of A Ω[A⁄Λ]) (0 : ℕ) (0 : ℤ) rfl).hom)

/-- `naiveCotangentToKaehler` is the derived image of the extended `toKaehler`
augmentation. -/
theorem naiveCotangentToKaehler_eq :
    naiveCotangentToKaehler =
      DerivedCategory.Q.map
        (extendMap
            ((ChainComplex.toSingle₀Equiv (Algebra.naiveCotangent Λ A)
                (ModuleCat.of A Ω[A⁄Λ])).symm
              ⟨ModuleCat.ofHom (Generators.self Λ A).toExtension.toKaehler,
                toKaehler_comp_d⟩)
            embeddingDownNat ≫
          (extendSingleIso embeddingDownNat (ModuleCat.of A Ω[A⁄Λ])
            (0 : ℕ) (0 : ℤ) rfl).hom) :=
  sorry

variable {B : Type u} [CommRing B] [Algebra Λ B]

/-- Target-changing comparison `NL{A⁄Λ} ⟶ Res_A(NL{B⁄Λ})` along a `Λ`-algebra
map `A → B`. -/
def naiveCotangentRestrictMap (φ : A →ₐ[Λ] B) :
    Algebra.naiveCotangentObject Λ A ⟶
      (ModuleCat.derivedRestrictionOfScalars φ.toRingHom).obj
        (Algebra.naiveCotangentObject Λ B) :=
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  let _ : IsScalarTower Λ A B := IsScalarTower.of_algHom φ
  let chain :=
    Algebra.Extension.NaiveCotangent.RestrictScalars.map
      (Generators.defaultHom (Generators.self Λ A) (Generators.self Λ B)).toExtensionHom
  DerivedCategory.Q.map (extendMap chain embeddingDownNat) ≫
    DerivedCategory.Q.map
      (ComplexShape.Embedding.mapAppIso embeddingDownNat
        (ModuleCat.restrictScalars φ.toRingHom)
        (Algebra.naiveCotangent Λ B)).inv ≫
    (ModuleCat.restrictScalars φ.toRingHom).mapDerivedCategoryFactors.inv.app
      ((Algebra.naiveCotangent Λ B).extend embeddingDownNat)

/-- `naiveCotangentRestrictMap φ` is the derived image of the target-changing
self-presentation map, transported to derived restriction. -/
theorem naiveCotangentRestrictMap_eq (φ : A →ₐ[Λ] B) :
    naiveCotangentRestrictMap φ =
      let _ : Algebra A B := φ.toRingHom.toAlgebra
      let _ : IsScalarTower Λ A B := IsScalarTower.of_algHom φ
      let chain :=
        Algebra.Extension.NaiveCotangent.RestrictScalars.map
          (Generators.defaultHom (Generators.self Λ A)
            (Generators.self Λ B)).toExtensionHom
      DerivedCategory.Q.map (extendMap chain embeddingDownNat) ≫
        DerivedCategory.Q.map
          (ComplexShape.Embedding.mapAppIso embeddingDownNat
            (ModuleCat.restrictScalars φ.toRingHom)
            (Algebra.naiveCotangent Λ B)).inv ≫
        (ModuleCat.restrictScalars φ.toRingHom).mapDerivedCategoryFactors.inv.app
          ((Algebra.naiveCotangent Λ B).extend embeddingDownNat) :=
  sorry

end Algebra.NaiveCotangent

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S}

/-- The identity comparison for derived restriction of scalars along `id`. -/
def derivedRestrictionIdIso (A : Type u) [CommRing A] :
    ModuleCat.derivedRestrictionOfScalars (RingHom.id A) ≅
      𝟭 (DerivedCategory (ModuleCat A)) :=
  Localization.liftNatIso
    (DerivedCategory.Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ))
    ((ModuleCat.restrictScalars (RingHom.id A)).mapHomologicalComplex (up ℤ) ⋙
      DerivedCategory.Q)
    DerivedCategory.Q
    (ModuleCat.derivedRestrictionOfScalars (RingHom.id A))
    (𝟭 (DerivedCategory (ModuleCat.{u} A)))
    (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId A) (up ℤ))
        DerivedCategory.Q ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} A) (up ℤ))
        DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q)

/-- `derivedRestrictionIdIso` is the localization lift of restriction along `id`. -/
theorem derivedRestrictionIdIso_eq (A : Type u) [CommRing A] :
    derivedRestrictionIdIso A =
      Localization.liftNatIso
        (DerivedCategory.Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ _)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ))
        ((ModuleCat.restrictScalars (RingHom.id A)).mapHomologicalComplex (up ℤ) ⋙
          DerivedCategory.Q)
        DerivedCategory.Q
        (ModuleCat.derivedRestrictionOfScalars (RingHom.id A))
        (𝟭 (DerivedCategory (ModuleCat.{u} A)))
        (Functor.isoWhiskerRight
            (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId A) (up ℤ))
            DerivedCategory.Q ≪≫
          Functor.isoWhiskerRight
            (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} A) (up ℤ))
            DerivedCategory.Q ≪≫
          Functor.leftUnitor DerivedCategory.Q) :=
  sorry

/-- Universe lift of `Inf_x`, matching the Hom-universe of derived Ext. -/
def infFunctorUlift {A : CommRingCat.{u}} {σA : Spec A ⟶ S} [HasStrongRimSchlessinger X]
    (x : X.p.Fiber (Over.mk σA)) :
    ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A :=
  infFunctor x ⋙ ModuleCat.uliftFunctor.{u + 1, u} A

/-- `infFunctorUlift` is `infFunctor` composed with universe lift. -/
theorem infFunctorUlift_eq {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    [HasStrongRimSchlessinger X] (x : X.p.Fiber (Over.mk σA)) :
    infFunctorUlift x = infFunctor x ⋙ ModuleCat.uliftFunctor.{u + 1, u} A :=
  sorry

/-- The degree-zero Ext class of a derived morphism `K ⟶ M[0]`, as the
corresponding `ShiftedHom` in degree `0`. -/
def extClass {A : Type u} [CommRing A] {K : DerivedCategory (ModuleCat.{u} A)}
    {M : ModuleCat.{u} A}
    (f : K ⟶ (singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj M) :
    (DerivedCategory.Ext.moduleFunctor K (0 : ℤ)).obj M :=
  ShiftedHom.mk₀ (0 : ℤ) rfl f

/-- `extClass` is `ShiftedHom.mk₀` of a derived morphism into a single object. -/
theorem extClass_eq {A : Type u} [CommRing A] {K : DerivedCategory (ModuleCat.{u} A)}
    {M : ModuleCat.{u} A}
    (f : K ⟶ (singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj M) :
    extClass f = ShiftedHom.mk₀ (0 : ℤ) rfl f :=
  sorry

/-- The Ext map `Res_A(Ext^i_B(E_y, N)) ⟶ Ext^i_A(E_x, Res_A N)` induced by
restriction of scalars and a functoriality map `E_x ⟶ Res_A(E_y)`. -/
def extMapOfRestriction {A B : Type u} [CommRing A] [CommRing B] {σ : A →+* B}
    {Kx : DerivedCategory (ModuleCat.{u} A)} {Ky : DerivedCategory (ModuleCat.{u} B)}
    (f : Kx ⟶ (ModuleCat.derivedRestrictionOfScalars σ).obj Ky) (i : ℤ)
    (N : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars.{u + 1} σ).obj
        ((DerivedCategory.Ext.moduleFunctor Ky i).obj N) ⟶
      (DerivedCategory.Ext.moduleFunctor Kx i).obj
        ((ModuleCat.restrictScalars σ).obj N) :=
  ConcreteCategory.ofHom
    { toFun := fun α ↦
        f ≫ (ModuleCat.derivedRestrictionOfScalars σ).map α ≫
          ((ModuleCat.derivedRestrictionOfScalars σ).commShiftIso i).hom.app
            ((singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj N) ≫
          ((ModuleCat.DerivedRestriction.singleIso σ (0 : ℤ) N).hom)⟦i⟧'
      map_add' := sorry
      map_smul' := sorry }

/-- `extMapOfRestriction` is precomposition with `E_x ⟶ Res_A(E_y)` after
transporting Ext classes along derived restriction, the shift comparison, and
`singleIso`. -/
theorem extMapOfRestriction_eq {A B : Type u} [CommRing A] [CommRing B]
    {σ : A →+* B} {Kx : DerivedCategory (ModuleCat.{u} A)}
    {Ky : DerivedCategory (ModuleCat.{u} B)}
    (f : Kx ⟶ (ModuleCat.derivedRestrictionOfScalars σ).obj Ky) (i : ℤ)
    (N : ModuleCat.{u} B)
    (α : (ModuleCat.restrictScalars.{u + 1} σ).obj
      ((DerivedCategory.Ext.moduleFunctor Ky i).obj N)) :
    extMapOfRestriction f i N α =
      f ≫ (ModuleCat.derivedRestrictionOfScalars σ).map α ≫
        ((ModuleCat.derivedRestrictionOfScalars σ).commShiftIso i).hom.app
          ((singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj N) ≫
        ((ModuleCat.DerivedRestriction.singleIso σ (0 : ℤ) N).hom)⟦i⟧' :=
  sorry

/-- Universe-lifted restriction of scalars commutes with `uliftFunctor`. -/
def uliftRestrictScalarsIso {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B) :
    ModuleCat.restrictScalars.{u} σ ⋙ ModuleCat.uliftFunctor.{u + 1, u} A ≅
      ModuleCat.uliftFunctor.{u + 1, u} B ⋙ ModuleCat.restrictScalars.{u + 1} σ :=
  NatIso.ofComponents
    (fun M ↦
      { hom := ConcreteCategory.ofHom
          { toFun := fun x ↦ x
            map_add' := sorry
            map_smul' := sorry }
        inv := ConcreteCategory.ofHom
          { toFun := fun x ↦ x
            map_add' := sorry
            map_smul' := sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun {X Y} f ↦ sorry)

/-- `uliftRestrictScalarsIso` acts as the identity on the underlying `ULift`
carrier. -/
theorem uliftRestrictScalarsIso_hom_app {A B : Type u} [CommRing A] [CommRing B]
    (σ : A →+* B) (M : ModuleCat.{u} B)
    (x : (ModuleCat.restrictScalars.{u} σ ⋙
        ModuleCat.uliftFunctor.{u + 1, u} A).obj M) :
    (uliftRestrictScalarsIso σ).hom.app M x = x :=
  sorry

/-- Comparison `kaehlerObj` with `Ω[A⁄Λ]`, via the universal property of
bundled Kähler differentials. -/
def kaehlerCompare (ξ : ObjectOverAffineOpen X) :
    kaehlerObj ξ.algebraHom ⟶ ModuleCat.of ξ.carrier Ω[ξ.carrier ⁄ ξ.base] :=
  ModuleCat.Derivation.desc
    (ModuleCat.Derivation.mk (fun b ↦ KaehlerDifferential.D ξ.base ξ.carrier b)
      sorry sorry sorry)

/-- `kaehlerCompare` sends the bundled universal derivation to `d_{A⁄Λ}`. -/
theorem kaehlerCompare_d (ξ : ObjectOverAffineOpen X) (a : ξ.carrier) :
    kaehlerCompare ξ (kaehlerD ξ.algebraHom a) =
      KaehlerDifferential.D ξ.base ξ.carrier a :=
  sorry

/-- Identification of `NL{B⁄η.base}` with `NL{B⁄ξ.base}` along a shared affine
open. -/
theorem Hom.naiveCotangentObject_eq {ξ η : ObjectOverAffineOpen X}
    (f : ObjectOverAffineOpen.Hom ξ η) :
    Algebra.naiveCotangentObject η.base η.carrier =
      @Algebra.naiveCotangentObject ξ.base η.carrier _ _ f.algebra :=
  sorry

/-- Target-changing comparison along a morphism of objects through a shared
affine open. -/
def Hom.naiveCotangentRestrictMap {ξ η : ObjectOverAffineOpen X}
    (f : ObjectOverAffineOpen.Hom ξ η) :
    Algebra.naiveCotangentObject ξ.base ξ.carrier ⟶
      (ModuleCat.derivedRestrictionOfScalars f.toRingHom).obj
        (@Algebra.naiveCotangentObject ξ.base η.carrier _ _ f.algebra) :=
  @Algebra.NaiveCotangent.naiveCotangentRestrictMap ξ.base ξ.carrier _ _ ξ.algebra
    η.carrier _ f.algebra f.algHom

/-- `Hom.naiveCotangentRestrictMap` is `naiveCotangentRestrictMap` of `algHom`. -/
theorem Hom.naiveCotangentRestrictMap_eq {ξ η : ObjectOverAffineOpen X}
    (f : ObjectOverAffineOpen.Hom ξ η) :
    Hom.naiveCotangentRestrictMap f =
      @Algebra.NaiveCotangent.naiveCotangentRestrictMap ξ.base ξ.carrier _ _ ξ.algebra
        η.carrier _ f.algebra f.algHom :=
  sorry

/-- `infMap` along a morphism of objects through a shared affine open. -/
def infMapAlong {ξ η : ObjectOverAffineOpen X} [HasStrongRimSchlessinger X]
    (f : ObjectOverAffineOpen.Hom ξ η)
    {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
    (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N)
    (φ : Chosen.reindexObj X.p
      (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
      ξ.toObjectOverSpec.toFiber ⟶ η.toObjectOverSpec.toFiber) :
    (infFunctor ξ.toObjectOverSpec.toFiber).obj M ⟶
      (ModuleCat.restrictScalars f.toRingHom).obj
        ((infFunctor η.toObjectOverSpec.toFiber).obj N) :=
  AlgebraicGeometry.GroupoidsOver.infMap (CommRingCat.ofHom f.toRingHom) f.toS_comp g
    ξ.toObjectOverSpec.toFiber η.toObjectOverSpec.toFiber φ

/-- `infMapAlong` is `infMap` of the stored ring homomorphism. -/
theorem infMapAlong_eq {ξ η : ObjectOverAffineOpen X} [HasStrongRimSchlessinger X]
    (f : ObjectOverAffineOpen.Hom ξ η)
    {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
    (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N)
    (φ : Chosen.reindexObj X.p
      (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
      ξ.toObjectOverSpec.toFiber ⟶ η.toObjectOverSpec.toFiber) :
    infMapAlong f g φ =
      AlgebraicGeometry.GroupoidsOver.infMap (CommRingCat.ofHom f.toRingHom) f.toS_comp g
        ξ.toObjectOverSpec.toFiber η.toObjectOverSpec.toFiber φ :=
  sorry

/-- `tangentMap` along a morphism of objects through a shared affine open. -/
def tangentMapAlong {ξ η : ObjectOverAffineOpen X} [HasStrongRimSchlessinger X]
    (f : ObjectOverAffineOpen.Hom ξ η)
    {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
    (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N)
    (φ : Chosen.reindexObj X.p
      (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
      ξ.toObjectOverSpec.toFiber ⟶ η.toObjectOverSpec.toFiber) :
    (tangentFunctor ξ.toObjectOverSpec.toFiber).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} f.toRingHom).obj
        ((tangentFunctor η.toObjectOverSpec.toFiber).obj N) :=
  AlgebraicGeometry.GroupoidsOver.tangentMap (CommRingCat.ofHom f.toRingHom) f.toS_comp g
    ξ.toObjectOverSpec.toFiber η.toObjectOverSpec.toFiber φ

/-- `tangentMapAlong` is `tangentMap` of the stored ring homomorphism. -/
theorem tangentMapAlong_eq {ξ η : ObjectOverAffineOpen X} [HasStrongRimSchlessinger X]
    (f : ObjectOverAffineOpen.Hom ξ η)
    {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
    (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N)
    (φ : Chosen.reindexObj X.p
      (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
      ξ.toObjectOverSpec.toFiber ⟶ η.toObjectOverSpec.toFiber) :
    tangentMapAlong f g φ =
      AlgebraicGeometry.GroupoidsOver.tangentMap (CommRingCat.ofHom f.toRingHom)
        f.toS_comp g ξ.toObjectOverSpec.toFiber η.toObjectOverSpec.toFiber φ :=
  sorry

/-- A naive obstruction theory on a category fibred in groupoids satisfying
(RS*): complexes `E_x ∈ D⁻(A)`, maps `ξ_x : E_x ⟶ NL{A⁄Λ}`, identifications of
`Inf_x` and `T_x` with derived Ext, and functoriality maps in `D(A)`. -/
structure NaiveObstructionTheory (X : GroupoidsOver S)
    [HasStrongRimSchlessinger X] where
  /-- The complex `E_x` in `D⁻(A)`. -/
  complex : (ξ : ObjectOverAffineOpen X) → Minus (ModuleCat.{u} ξ.carrier)
  /-- The obstruction map `ξ_x : E_x ⟶ NL{A⁄Λ}`. -/
  obstructionMap : (ξ : ObjectOverAffineOpen X) →
    Minus.ι.obj (complex ξ) ⟶ Algebra.naiveCotangentObject ξ.base ξ.carrier
  /-- Functoriality map `E_x ⟶ Res_A(E_y)` in `D(A)` along `A → B`. -/
  map : {ξ η : ObjectOverAffineOpen X} → (f : ObjectOverAffineOpen.Hom ξ η) →
    Minus.ι.obj (complex ξ) ⟶
      (ModuleCat.derivedRestrictionOfScalars f.toRingHom).obj
        (Minus.ι.obj (complex η))
  /-- Isomorphism `Inf_x(-) ≅ Ext^{-1}_A(E_x, -)` after universe lift of Inf. -/
  infIso : (ξ : ObjectOverAffineOpen X) →
    infFunctorUlift ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (-1)
  /-- Isomorphism `T_x(-) ≅ Ext^0_A(E_x, -)`. -/
  tangentIso : (ξ : ObjectOverAffineOpen X) →
    tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (0 : ℤ)
  /-- Identity morphisms act as identity on `E_x` after restriction along `id`. -/
  map_id : ∀ ξ : ObjectOverAffineOpen X,
    map (ObjectOverAffineOpen.Hom.id ξ) =
      (derivedRestrictionIdIso ξ.carrier).inv.app (Minus.ι.obj (complex ξ))
  /-- Functoriality maps are compatible with composition, after the canonical
  iterated-restriction comparison. -/
  map_comp : ∀ {ξ η ζ : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η) (g : ObjectOverAffineOpen.Hom η ζ),
    map (ObjectOverAffineOpen.Hom.comp f g) =
      map f ≫ (ModuleCat.derivedRestrictionOfScalars f.toRingHom).map (map g) ≫
        (ModuleCat.DerivedRestriction.compIso f.toRingHom g.toRingHom).inv.app
          (Minus.ι.obj (complex ζ))
  /-- Diagram (i): `ξ_x` and `ξ_y` commute with functoriality of `E` and `NL`
  in `D(A)`. -/
  obstructionMap_natural : ∀ {ξ η : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η),
    map f ≫ (ModuleCat.derivedRestrictionOfScalars f.toRingHom).map
        (obstructionMap η ≫ eqToHom (Hom.naiveCotangentObject_eq f)) =
      obstructionMap ξ ≫ Hom.naiveCotangentRestrictMap f
  /-- The identifications `Inf_x ≅ Ext^{-1}(E_x, -)` commute with `infMap` and
  the Ext map induced by `g` and `E_x ⟶ Res_A(E_y)`. -/
  infIso_natural : ∀ {ξ η : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η)
      {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
      (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N),
    (infIso ξ).hom.app M ≫
        (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (-1)).map g =
      (ModuleCat.uliftFunctor.{u + 1, u} ξ.carrier).map
          (infMapAlong f g f.fiberArrow) ≫
        (uliftRestrictScalarsIso f.toRingHom).hom.app
          ((infFunctor η.toObjectOverSpec.toFiber).obj N) ≫
          (ModuleCat.restrictScalars.{u + 1} f.toRingHom).map ((infIso η).hom.app N) ≫
            extMapOfRestriction (map f) (-1) N
  /-- The identifications `T_x ≅ Ext^0(E_x, -)` commute with `tangentMap` and
  the Ext map induced by `g` and `E_x ⟶ Res_A(E_y)`. -/
  tangentIso_natural : ∀ {ξ η : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η)
      {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
      (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N),
    (tangentIso ξ).hom.app M ≫
        (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (0 : ℤ)).map g =
      tangentMapAlong f g f.fiberArrow ≫
        (ModuleCat.restrictScalars.{u + 1} f.toRingHom).map ((tangentIso η).hom.app N) ≫
          extMapOfRestriction (map f) (0 : ℤ) N
  /-- The composition `E_x ⟶ NL{A⁄Λ} ⟶ Ω[A⁄Λ]` is the Ext class of the
  canonical element of `T_x(Ω[A⁄Λ])`. -/
  canonical_compat : ∀ ξ : ObjectOverAffineOpen X,
    (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (0 : ℤ)).map
          (kaehlerCompare ξ)
        ((tangentIso ξ).hom.app (kaehlerObj ξ.algebraHom)
          (canonicalElement ξ.algebraHom ξ.factor ξ.toObjectOverSpec.toFiber
            ξ.isOpenImmersion)) =
      extClass (obstructionMap ξ ≫ Algebra.NaiveCotangent.naiveCotangentToKaehler)
  /-- Lifts of `x` to `A'` exist if and only if
  `E_x ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}` vanishes. -/
  lifts_iff : ∀ {ξ : ObjectOverAffineOpen X} (τ : DeformationSituation.OverAffine ξ),
    obstructionMap ξ ≫
        @Algebra.NaiveCotangent.naiveCotangentMap ξ.base τ.situation.source ξ.carrier
          _ _ _ τ.algebra ξ.algebra τ.algHom = 0 ↔
      Nonempty (DeformationSituation.ObjectLift τ.situation)

namespace NaiveObstructionTheory

variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

/-- Package complexes, obstruction maps, functoriality maps, and Inf/T
identifications as a naive obstruction theory; the naturality, composition,
canonical-element, and lifting laws are deferred. -/
def of
    (complex : (ξ : ObjectOverAffineOpen X) → Minus (ModuleCat.{u} ξ.carrier))
    (obstructionMap : (ξ : ObjectOverAffineOpen X) →
      Minus.ι.obj (complex ξ) ⟶ Algebra.naiveCotangentObject ξ.base ξ.carrier)
    (map : {ξ η : ObjectOverAffineOpen X} → (f : ObjectOverAffineOpen.Hom ξ η) →
      Minus.ι.obj (complex ξ) ⟶
        (ModuleCat.derivedRestrictionOfScalars f.toRingHom).obj
          (Minus.ι.obj (complex η)))
    (infIso : (ξ : ObjectOverAffineOpen X) →
      infFunctorUlift ξ.toObjectOverSpec.toFiber ≅
        DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (-1))
    (tangentIso : (ξ : ObjectOverAffineOpen X) →
      tangentFunctor ξ.toObjectOverSpec.toFiber ≅
        DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (0 : ℤ)) :
    NaiveObstructionTheory X where
  complex := complex
  obstructionMap := obstructionMap
  map := map
  infIso := infIso
  tangentIso := tangentIso
  map_id := sorry
  map_comp := sorry
  obstructionMap_natural := sorry
  infIso_natural := sorry
  tangentIso_natural := sorry
  canonical_compat := sorry
  lifts_iff := sorry

/-- Condition (i): `ξ_x` and `ξ_y` commute with functoriality of `E` and `NL`. -/
theorem spec_obstructionMap_natural (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η) :
    𝒪.map f ≫ (ModuleCat.derivedRestrictionOfScalars f.toRingHom).map
        (𝒪.obstructionMap η ≫ eqToHom (Hom.naiveCotangentObject_eq f)) =
      𝒪.obstructionMap ξ ≫ Hom.naiveCotangentRestrictMap f :=
  sorry

/-- Condition (ii): functoriality maps compose after iterated-restriction
comparison. -/
theorem spec_map_comp (𝒪 : NaiveObstructionTheory X)
    {ξ η ζ : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    (g : ObjectOverAffineOpen.Hom η ζ) :
    𝒪.map (ObjectOverAffineOpen.Hom.comp f g) =
      𝒪.map f ≫
        (ModuleCat.derivedRestrictionOfScalars f.toRingHom).map (𝒪.map g) ≫
          (ModuleCat.DerivedRestriction.compIso f.toRingHom g.toRingHom).inv.app
            (Minus.ι.obj (𝒪.complex ζ)) :=
  sorry

/-- Condition (iii): Inf identifications commute with `infMap` and
`E_x ⟶ Res_A(E_y)`. -/
theorem spec_infIso_natural (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
    (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N) :
    (𝒪.infIso ξ).hom.app M ≫
        (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) (-1)).map g =
      (ModuleCat.uliftFunctor.{u + 1, u} ξ.carrier).map
          (infMapAlong f g f.fiberArrow) ≫
        (uliftRestrictScalarsIso f.toRingHom).hom.app
          ((infFunctor η.toObjectOverSpec.toFiber).obj N) ≫
          (ModuleCat.restrictScalars.{u + 1} f.toRingHom).map ((𝒪.infIso η).hom.app N) ≫
            extMapOfRestriction (𝒪.map f) (-1) N :=
  sorry

/-- Condition (iii): T identifications commute with `tangentMap` and
`E_x ⟶ Res_A(E_y)`. -/
theorem spec_tangentIso_natural (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
    (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N) :
    (𝒪.tangentIso ξ).hom.app M ≫
        (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) (0 : ℤ)).map g =
      tangentMapAlong f g f.fiberArrow ≫
        (ModuleCat.restrictScalars.{u + 1} f.toRingHom).map ((𝒪.tangentIso η).hom.app N) ≫
          extMapOfRestriction (𝒪.map f) (0 : ℤ) N :=
  sorry

/-- Condition (iv): the image of the canonical element under `tangentIso` is the
Ext class of `ξ_x ≫ NL ⟶ Ω`. -/
theorem spec_canonical_compat (𝒪 : NaiveObstructionTheory X)
    (ξ : ObjectOverAffineOpen X) :
    (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) (0 : ℤ)).map
          (kaehlerCompare ξ)
        ((𝒪.tangentIso ξ).hom.app (kaehlerObj ξ.algebraHom)
          (canonicalElement ξ.algebraHom ξ.factor ξ.toObjectOverSpec.toFiber
            ξ.isOpenImmersion)) =
      extClass (𝒪.obstructionMap ξ ≫
        Algebra.NaiveCotangent.naiveCotangentToKaehler) :=
  sorry

/-- The functor `M ↦ Ext^i_A(E_x, M)`. -/
def extFunctor (𝒪 : NaiveObstructionTheory X) (ξ : ObjectOverAffineOpen X)
    (i : ℤ) : ModuleCat.{u} ξ.carrier ⥤ ModuleCat.{u + 1} ξ.carrier :=
  DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) i

/-- The value of `extFunctor` on a coefficient module. -/
theorem extFunctor_obj (𝒪 : NaiveObstructionTheory X)
    (ξ : ObjectOverAffineOpen X) (i : ℤ) (M : ModuleCat.{u} ξ.carrier) :
    (𝒪.extFunctor ξ i).obj M =
      (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) i).obj M :=
  sorry

/-- The obstruction-module functor `O_x(-) = Ext^1_A(E_x, -)`. -/
def obstructionModule (𝒪 : NaiveObstructionTheory X)
    (ξ : ObjectOverAffineOpen X) :
    ModuleCat.{u} ξ.carrier ⥤ ModuleCat.{u + 1} ξ.carrier :=
  𝒪.extFunctor ξ 1

/-- `obstructionModule` is `Ext^1_A(E_x, -)`. -/
theorem obstructionModule_obj (𝒪 : NaiveObstructionTheory X)
    (ξ : ObjectOverAffineOpen X) (M : ModuleCat.{u} ξ.carrier) :
    (𝒪.obstructionModule ξ).obj M =
      (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) 1).obj M :=
  sorry

/-- Condition (v): the composite `E_x ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}` vanishes if and
only if `x` lifts to `A'`. -/
theorem lifts_iff_zero (𝒪 : NaiveObstructionTheory X)
    {ξ : ObjectOverAffineOpen X} (τ : DeformationSituation.OverAffine ξ) :
    𝒪.obstructionMap ξ ≫
        @Algebra.NaiveCotangent.naiveCotangentMap ξ.base τ.situation.source ξ.carrier
          _ _ _ τ.algebra ξ.algebra τ.algHom = 0 ↔
      Nonempty (DeformationSituation.ObjectLift τ.situation) :=
  sorry

end NaiveObstructionTheory

end AlgebraicGeometry.GroupoidsOver
