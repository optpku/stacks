module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObjectOverAffineOpen
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Lifts
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.Functoriality
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalElement
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Augmentation
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.DerivedFunctoriality
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.SquareZeroComparison
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import ReasLib.Algebra.Category.ModuleCat.Ulift.Restriction
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Naive obstruction theories for categories fibred in groupoids -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Universe lift of `Inf_x`, matching the Hom-universe of derived Ext. -/
def infFunctorUlift {A : CommRingCat.{u}} {σA : Spec A ⟶ S} [HasStrongRimSchlessinger X]
    (x : X.p.Fiber (Over.mk σA)) :
    ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A :=
  infFunctor x ⋙ ModuleCat.uliftFunctor.{u + 1, u} A

/-- Identification of `NL{B⁄η.base}` with `NL{B⁄ξ.base}` along a shared affine
open. -/
theorem ObjectOverAffineOpen.Hom.naiveCotangentObject_eq {ξ η : ObjectOverAffineOpen X}
    (f : ObjectOverAffineOpen.Hom ξ η) :
    Algebra.naiveCotangentObject η.base η.carrier =
      @Algebra.naiveCotangentObject ξ.base η.carrier _ _ f.algebra :=
  sorry

/-- A naive obstruction theory on a category fibred in groupoids satisfying
(RS*): complexes `E_x ∈ D⁻(A)`, maps `ξ_x : E_x ⟶ NL{A⁄Λ}`, identifications of
`Inf_x` and `T_x` with derived Ext, and functoriality maps in `D(A)`. -/
structure NaiveObstructionTheory {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : GroupoidsOver S)
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
  /-- Functoriality maps are compatible with composition, after the canonical
  iterated-restriction comparison. -/
  map_comp : ∀ {ξ η ζ : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η) (g : ObjectOverAffineOpen.Hom η ζ),
    map (ObjectOverAffineOpen.Hom.comp f g) =
      map f ≫ (ModuleCat.derivedRestrictionOfScalars f.toRingHom).map (map g) ≫
        (ModuleCat.DerivedRestriction.compIso f.toRingHom g.toRingHom).inv.app
          (Minus.ι.obj (complex ζ))
  /-- Obstruction morphisms commute with restriction of scalars and cotangent functoriality. -/
  obstructionMap_natural : ∀ {ξ η : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η),
    map f ≫ (ModuleCat.derivedRestrictionOfScalars f.toRingHom).map
        (obstructionMap η ≫ eqToHom (ObjectOverAffineOpen.Hom.naiveCotangentObject_eq f)) =
      obstructionMap ξ ≫ (@Algebra.NaiveCotangent.naiveCotangentRestrictMap ξ.base ξ.carrier _ _ ξ.algebra
        η.carrier _ f.algebra f.algHom)
  /-- The identifications `Inf_x ≅ Ext^{-1}(E_x, -)` commute with `infMap` and
  the Ext map induced by `g` and `E_x ⟶ Res_A(E_y)`. -/
  infIso_natural : ∀ {ξ η : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η)
      {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
      (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N),
    (infIso ξ).hom.app M ≫
        (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (-1)).map g =
      (ModuleCat.uliftFunctor.{u + 1, u} ξ.carrier).map
          (infMap (CommRingCat.ofHom f.toRingHom) f.toS_comp g
            ξ.toObjectOverSpec.toFiber η.toObjectOverSpec.toFiber f.fiberArrow) ≫
        (ModuleCat.uliftRestrictScalarsIso f.toRingHom).hom.app
          ((infFunctor η.toObjectOverSpec.toFiber).obj N) ≫
          (ModuleCat.restrictScalars.{u + 1} f.toRingHom).map ((infIso η).hom.app N) ≫
            DerivedCategory.Ext.restrictionMap (map f) (-1) N
  /-- The identifications `T_x ≅ Ext^0(E_x, -)` commute with `tangentMap` and
  the Ext map induced by `g` and `E_x ⟶ Res_A(E_y)`. -/
  tangentIso_natural : ∀ {ξ η : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η)
      {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
      (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N),
    (tangentIso ξ).hom.app M ≫
        (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (0 : ℤ)).map g =
      tangentMap (CommRingCat.ofHom f.toRingHom) f.toS_comp g
          ξ.toObjectOverSpec.toFiber η.toObjectOverSpec.toFiber f.fiberArrow ≫
        (ModuleCat.restrictScalars.{u + 1} f.toRingHom).map ((tangentIso η).hom.app N) ≫
          DerivedCategory.Ext.restrictionMap (map f) (0 : ℤ) N
  /-- The composition `E_x ⟶ NL{A⁄Λ} ⟶ Ω[A⁄Λ]` is the Ext class of the
  canonical element of `T_x(Ω[A⁄Λ])`. -/
  canonical_compat : ∀ ξ : ObjectOverAffineOpen X,
    (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (complex ξ)) (0 : ℤ)).map
          (ObjectOverAffineOpen.kaehlerCompare ξ)
        ((tangentIso ξ).hom.app (CommRingCat.KaehlerDifferential ξ.algebraHom)
          (canonicalElement ξ.algebraHom ξ.factor ξ.toObjectOverSpec.toFiber
            ξ.isOpenImmersion)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (obstructionMap ξ ≫ Algebra.NaiveCotangent.naiveCotangentToKaehler)
  /-- Lifts of `x` to `A'` exist if and only if
  `E_x ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}` vanishes. -/
  lifts_iff : ∀ {ξ : ObjectOverAffineOpen X} (τ : DeformationSituation.OverAffine ξ),
    obstructionMap ξ ≫
        @Algebra.NaiveCotangent.naiveCotangentMap ξ.base τ.situation.source ξ.carrier
          _ _ _ τ.algebra ξ.algebra τ.algHom = 0 ↔
      Nonempty (DeformationSituation.ObjectLift τ.situation)

namespace NaiveObstructionTheory

variable [IsLocallyNoetherian S] [HasStrongRimSchlessinger X]

/-- The obstruction-module functor `O_x(-) = Ext^1_A(E_x, -)`. -/
def obstructionModule (𝒪 : NaiveObstructionTheory X)
    (ξ : ObjectOverAffineOpen X) :
    ModuleCat.{u} ξ.carrier ⥤ ModuleCat.{u + 1} ξ.carrier :=
  DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) 1

/-- `obstructionModule` is `Ext^1_A(E_x, -)`. -/
theorem obstructionModule_obj (𝒪 : NaiveObstructionTheory X)
    (ξ : ObjectOverAffineOpen X) (M : ModuleCat.{u} ξ.carrier) :
    (𝒪.obstructionModule ξ).obj M =
      (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) 1).obj M :=
  rfl

end NaiveObstructionTheory

end AlgebraicGeometry.GroupoidsOver
