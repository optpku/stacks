/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing
public import ReasLib.Algebra.Module.RelativeDualizing.Comparison
public import ReasLib.Algebra.Module.RelativeDualizing.Localization
public import ReasLib.RingTheory.RingHom.FiniteType.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace Algebra.RelativeDualizingModule

/-- An explicit finite/open presentation of a homomorphism of commutative rings. -/
structure Presentation {A B : CommRingCat.{u}} (phi : A ⟶ B) where
  /-- The finite intermediate algebra. -/
  finiteModel : CommRingCat.{u}
  /-- The map from the base to the finite model. -/
  toFinite : A ⟶ finiteModel
  /-- The map from the finite model to the target. -/
  toTarget : finiteModel ⟶ B
  /-- The two maps factor the presented homomorphism. -/
  fac : toFinite ≫ toTarget = phi
  /-- The intermediate algebra is finite over the base. -/
  finite : @Module.Finite A finiteModel _ _
    (@Algebra.toModule A finiteModel _ _ toFinite.hom.toAlgebra)
  /-- The target spectrum is open in the spectrum of the finite model. -/
  openImmersion : IsOpenImmersion (Spec.map toTarget)

namespace Presentation

/-- Construct a finite/open presentation from explicit ring maps and their defining laws. -/
def of {A B C : CommRingCat.{u}} {phi : A ⟶ B} (toFinite : A ⟶ C)
    (toTarget : C ⟶ B) (fac : toFinite ≫ toTarget = phi)
    (finite : @Module.Finite A C _ _
      (@Algebra.toModule A C _ _ toFinite.hom.toAlgebra))
    (openImmersion : IsOpenImmersion (Spec.map toTarget)) : Presentation phi where
  finiteModel := C
  toFinite := toFinite
  toTarget := toTarget
  fac := fac
  finite := finite
  openImmersion := openImmersion

/-- The algebra structures carried by a presentation form the required scalar tower. -/
theorem isScalarTower {A B : CommRingCat.{u}} {phi : A ⟶ B} (P : Presentation phi) :
    @IsScalarTower A P.finiteModel B P.toFinite.hom.toAlgebra.toSMul
      P.toTarget.hom.toAlgebra.toSMul phi.hom.toAlgebra.toSMul := sorry

/-- Finite-type quasi-finiteness for the presented ring map, in algebra form. -/
theorem quasiFinite {A B : CommRingCat.{u}} {phi : A ⟶ B} (P : Presentation phi)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) :
    @Algebra.FiniteType.QuasiFinite A B _ _ phi.hom.toAlgebra := sorry

/-- The relative dualizing module determined by an explicit finite/open presentation. -/
def module {A B : CommRingCat.{u}} {phi : A ⟶ B} (P : Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) : ModuleCat B :=
  @RelativeDualizingModule.of A P.finiteModel B _ _ _ hA hB
    P.toFinite.hom.toAlgebra P.toTarget.hom.toAlgebra phi.hom.toAlgebra
    (P.isScalarTower) (P.quasiFinite h) P.finite P.openImmersion

/-- The module of a presentation is the dual of its finite model extended to the target. -/
theorem module_eq {A B : CommRingCat.{u}} {phi : A ⟶ B} (P : Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) :
    P.module hA hB h =
      @RelativeDualizingModule.of A P.finiteModel B _ _ _ hA hB
        P.toFinite.hom.toAlgebra P.toTarget.hom.toAlgebra phi.hom.toAlgebra
        P.isScalarTower (P.quasiFinite h) P.finite P.openImmersion := sorry

/-- The original base action and the action through the finite model agree after simultaneous
principal localization. -/
theorem awayScalarTower {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (a : A) :
    @IsScalarTower A P.finiteModel (Localization.Away (phi.hom a))
      P.toFinite.hom.toAlgebra.toSMul
      (((algebraMap B (Localization.Away (phi.hom a))).comp
        P.toTarget.hom).toAlgebra.toSMul)
      (((algebraMap B (Localization.Away (phi.hom a))).comp
        phi.hom).toAlgebra.toSMul) := sorry

/-- The source localization and the original base action agree on the localized target. -/
theorem awayLocalizedScalarTower {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (a : A) :
    @IsScalarTower A (Localization.Away a) (Localization.Away (phi.hom a))
      (inferInstance : SMul A (Localization.Away a))
      (Localization.Away.Relative.mapAlgebra phi.hom a).toSMul
      (((algebraMap B (Localization.Away (phi.hom a))).comp
        phi.hom).toAlgebra.toSMul) := sorry

/-- The explicit map from the localized finite model to the localized target. -/
noncomputable def awayToTarget {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (a : A) :
    Localization.Away (P.toFinite.hom a) →+*
      Localization.Away (phi.hom a) :=
  @RelativeDualizingModule.awayFactorMap A P.finiteModel
    (Localization.Away (phi.hom a)) _ _ _ P.toFinite.hom.toAlgebra
    (((algebraMap B (Localization.Away (phi.hom a))).comp
      P.toTarget.hom).toAlgebra)
    (((algebraMap B (Localization.Away (phi.hom a))).comp
      phi.hom).toAlgebra)
    (awayScalarTower P a) a
    (Localization.Away.Relative.mapAlgebra phi.hom a)
    (awayLocalizedScalarTower a)

/-- The localized finite-model map and localized open map factor the localized ring map. -/
theorem away_fac {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (a : A) :
    CommRingCat.ofHom (Localization.awayMap P.toFinite.hom a) ≫
        CommRingCat.ofHom (awayToTarget P a) =
      CommRingCat.ofHom (Localization.awayMap phi.hom a) := sorry

/-- Principal localization preserves finiteness of the finite model. -/
theorem away_finite {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (a : A) :
    @Module.Finite (Localization.Away a)
      (Localization.Away (P.toFinite.hom a)) _ _
      (@Algebra.toModule (Localization.Away a)
        (Localization.Away (P.toFinite.hom a)) _ _
        (Localization.Away.Relative.mapAlgebra P.toFinite.hom a)) := sorry

/-- The map from the localized finite model to the localized target remains an open
immersion on spectra. -/
theorem away_openImmersion {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (a : A) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (awayToTarget P a))) := sorry

/-- Simultaneously localizing a finite-type quasi-finite map preserves that property. -/
theorem away_quasiFinite {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A) :
    RingHom.FiniteType.QuasiFinite (Localization.awayMap phi.hom a) := sorry

/-- The canonical base algebra structure on a target localization. -/
@[reducible]
def awayTargetAlgebra {A B : CommRingCat.{u}} (phi : A ⟶ B) (b : B) :
    Algebra A (Localization.Away b) :=
  @OreLocalization.instAlgebra B _ (Submonoid.powers b) _ A _ phi.hom.toAlgebra

/-- The canonical finite-model algebra structure on a target localization. -/
@[reducible]
def awayTargetFiniteAlgebra {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (b : B) : Algebra P.finiteModel (Localization.Away b) :=
  @OreLocalization.instAlgebra B _ (Submonoid.powers b) _ P.finiteModel _
    P.toTarget.hom.toAlgebra

/-- The original base action and the action through the finite model agree after
localizing only the target. -/
theorem awayTargetScalarTower {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (b : B) :
    @IsScalarTower A P.finiteModel (Localization.Away b)
      P.toFinite.hom.toAlgebra.toSMul
      (P.awayTargetFiniteAlgebra b).toSMul
      (awayTargetAlgebra phi b).toSMul := sorry

/-- Localizing only the target of a finite-type quasi-finite map preserves that
property. -/
theorem awayTarget_quasiFinite {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b : B) :
    RingHom.FiniteType.QuasiFinite
      ((algebraMap B (Localization.Away b)).comp phi.hom) := sorry

/-- The target-localized finite-model map factors the target-localized ring map. -/
theorem awayTarget_fac {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (b : B) :
    P.toFinite ≫ CommRingCat.ofHom
        ((algebraMap B (Localization.Away b)).comp P.toTarget.hom) =
      CommRingCat.ofHom
        ((algebraMap B (Localization.Away b)).comp phi.hom) := sorry

/-- The target-localized map from the finite model remains an open immersion on spectra. -/
theorem awayTarget_openImmersion {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (b : B) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        ((algebraMap B (Localization.Away b)).comp P.toTarget.hom))) := sorry

/-- The finite/open presentation obtained by localizing only its target ring. -/
noncomputable def awayTarget {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (b : B) :
    Presentation
      (CommRingCat.ofHom ((algebraMap B (Localization.Away b)).comp phi.hom)) where
  finiteModel := P.finiteModel
  toFinite := P.toFinite
  toTarget := CommRingCat.ofHom
    ((algebraMap B (Localization.Away b)).comp P.toTarget.hom)
  fac := awayTarget_fac P b
  finite := P.finite
  openImmersion := awayTarget_openImmersion P b

/-- The finite/open presentation obtained by simultaneously localizing the base, finite
model, and target at `a` and its images. -/
noncomputable def away {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (a : A) :
    Presentation (CommRingCat.ofHom (Localization.awayMap phi.hom a)) where
  finiteModel := CommRingCat.of (Localization.Away (P.toFinite.hom a))
  toFinite := CommRingCat.ofHom (Localization.awayMap P.toFinite.hom a)
  toTarget := CommRingCat.ofHom (awayToTarget P a)
  fac := away_fac P a
  finite := away_finite P hA a
  openImmersion := away_openImmersion P a

/-- The module of the localized presentation is canonically the localization of the original
relative dualizing module. -/
noncomputable def awayModuleIso {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A) :
    (P.away hA a).module inferInstance inferInstance (P.away_quasiFinite hA h a) ≅
      ModuleCat.of (Localization.Away (phi.hom a))
        (LocalizedModule.Away (phi.hom a) (P.module hA hB h)) :=
  @RelativeDualizingModule.awayIso A P.finiteModel B _ _ _
    P.toFinite.hom.toAlgebra P.toTarget.hom.toAlgebra phi.hom.toAlgebra
    P.isScalarTower hA hB (P.quasiFinite h) P.finite P.openImmersion a

/-- The canonical relative dualizing module after localizing only the target. -/
abbrev awayTargetModule {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b : B) :
    ModuleCat (Localization.Away b) :=
  @RelativeDualizingModule.of A P.finiteModel (Localization.Away b) _ _ _
    hA inferInstance P.toFinite.hom.toAlgebra
    (P.awayTargetFiniteAlgebra b)
    (awayTargetAlgebra phi b)
    (P.awayTargetScalarTower b)
    (@RelativeDualizingModule.quasiFiniteAwayTarget A B _ _
      phi.hom.toAlgebra hA hB (P.quasiFinite h) b) P.finite
    (@RelativeDualizingModule.openAwayTarget P.finiteModel B _ _
      P.toTarget.hom.toAlgebra P.openImmersion b)

/-- The module of the target-localized presentation is canonically the localization of the
original relative dualizing module. -/
noncomputable def awayTargetModuleIso {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b : B) :
    ModuleCat.of (Localization.Away b)
        (LocalizedModule.Away b (P.module hA hB h)) ≅
      P.awayTargetModule hA hB h b :=
  @RelativeDualizingModule.awayTargetIso A P.finiteModel B _ _ _
    P.toFinite.hom.toAlgebra P.toTarget.hom.toAlgebra phi.hom.toAlgebra
    P.isScalarTower hA hB (P.quasiFinite h) P.finite P.openImmersion b

/-- The target-localized presentation has the canonical target-localized module. -/
theorem awayTargetModule_eq {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b : B) :
    (P.awayTarget b).module hA inferInstance
        (P.awayTarget_quasiFinite hA hB h b) =
      P.awayTargetModule hA hB h b := sorry

/-- Additivity of canonical restriction after localizing only the target. -/
theorem awayTargetRestriction_map_add {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b : B)
    (x y : P.module hA hB h) :
    (P.awayTargetModuleIso hA hB h b).hom
        (LocalizedModule.mkLinearMap (Submonoid.powers b)
          (P.module hA hB h) (x + y)) =
      (P.awayTargetModuleIso hA hB h b).hom
          (LocalizedModule.mkLinearMap (Submonoid.powers b)
            (P.module hA hB h) x) +
        (P.awayTargetModuleIso hA hB h b).hom
          (LocalizedModule.mkLinearMap (Submonoid.powers b)
            (P.module hA hB h) y) := sorry

/-- Semilinearity of canonical restriction after localizing only the target. -/
theorem awayTargetRestriction_map_smul {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b r : B)
    (x : P.module hA hB h) :
    (P.awayTargetModuleIso hA hB h b).hom
        (LocalizedModule.mkLinearMap (Submonoid.powers b)
          (P.module hA hB h) (r • x)) =
      algebraMap B (Localization.Away b) r •
        (P.awayTargetModuleIso hA hB h b).hom
          (LocalizedModule.mkLinearMap (Submonoid.powers b)
            (P.module hA hB h) x) := sorry

/-- The canonical semilinear restriction to the target-localized presentation. -/
noncomputable def awayTargetRestriction {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b : B) :
    P.module hA hB h →ₛₗ[algebraMap B (Localization.Away b)]
      P.awayTargetModule hA hB h b where
  toFun x := (P.awayTargetModuleIso hA hB h b).hom
    (LocalizedModule.mkLinearMap (Submonoid.powers b) (P.module hA hB h) x)
  map_add' := awayTargetRestriction_map_add P hA hB h b
  map_smul' := awayTargetRestriction_map_smul P hA hB h b

/-- Additivity of the canonical principal-open restriction determined by
`awayModuleIso`. -/
theorem awayRestriction_map_add {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A)
    (x y : P.module hA hB h) :
    (P.awayModuleIso hA hB h a).inv
        (LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
          (P.module hA hB h) (x + y)) =
      (P.awayModuleIso hA hB h a).inv
          (LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
            (P.module hA hB h) x) +
        (P.awayModuleIso hA hB h a).inv
          (LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
            (P.module hA hB h) y) := sorry

/-- Semilinearity of the canonical principal-open restriction determined by
`awayModuleIso`. -/
theorem awayRestriction_map_smul {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A)
    (r : B) (x : P.module hA hB h) :
    (P.awayModuleIso hA hB h a).inv
        (LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
          (P.module hA hB h) (r • x)) =
      algebraMap B (Localization.Away (phi.hom a)) r •
        (P.awayModuleIso hA hB h a).inv
          (LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
            (P.module hA hB h) x) := sorry

/-- The canonical semilinear restriction from a presentation to its simultaneous
principal localization. -/
noncomputable def awayRestriction {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A) :
    P.module hA hB h →ₛₗ[algebraMap B (Localization.Away (phi.hom a))]
      (P.away hA a).module inferInstance inferInstance
        (P.away_quasiFinite hA h a) where
  toFun x := (P.awayModuleIso hA hB h a).inv
    (LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
      (P.module hA hB h) x)
  map_add' := awayRestriction_map_add P hA hB h a
  map_smul' := awayRestriction_map_smul P hA hB h a

/-- After `awayModuleIso`, canonical principal-open restriction is the usual map into
the localized module. -/
theorem awayRestriction_awayModuleIso {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A)
    (x : P.module hA hB h) :
    (P.awayModuleIso hA hB h a).hom (P.awayRestriction hA hB h a x) =
      LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
        (P.module hA hB h) x := sorry

/-- Transporting an affine section identification through principal restriction gives the
canonical semilinear map to the localized presentation. -/
noncomputable def awaySectionRestriction {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A) {M : ModuleCat B}
    (e : M ≅ P.module hA hB h) :
    M →ₛₗ[algebraMap B (Localization.Away (phi.hom a))]
      (P.away hA a).module inferInstance inferInstance
        (P.away_quasiFinite hA h a) :=
  (P.awayRestriction hA hB h a).comp e.hom.hom

/-- Under `awayModuleIso`, affine section restriction is the localization of the original
affine identification. -/
theorem awaySectionRestriction_awayModuleIso
    {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Presentation phi) (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A) {M : ModuleCat B}
    (e : M ≅ P.module hA hB h) (x : M) :
    (P.awayModuleIso hA hB h a).hom
        (P.awaySectionRestriction hA hB h a e x) =
      LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
        (P.module hA hB h) (e.hom x) := sorry

/-- The underlying ring homomorphism of an explicitly based refinement. -/
def refinementRingHom {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P Q : Presentation phi)
    (i : @AlgHom A P.finiteModel Q.finiteModel _ _ _
      P.toFinite.hom.toAlgebra Q.toFinite.hom.toAlgebra) :
    P.finiteModel →+* Q.finiteModel :=
  @AlgHom.toRingHom A P.finiteModel Q.finiteModel _ _ _
    P.toFinite.hom.toAlgebra Q.toFinite.hom.toAlgebra i

/-- The composite of two explicitly based refinements. -/
def refinementComp {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P₀ P₁ P₂ : Presentation phi)
    (i₀₁ : @AlgHom A P₀.finiteModel P₁.finiteModel _ _ _
      P₀.toFinite.hom.toAlgebra P₁.toFinite.hom.toAlgebra)
    (i₁₂ : @AlgHom A P₁.finiteModel P₂.finiteModel _ _ _
      P₁.toFinite.hom.toAlgebra P₂.toFinite.hom.toAlgebra) :
    @AlgHom A P₀.finiteModel P₂.finiteModel _ _ _
      P₀.toFinite.hom.toAlgebra P₂.toFinite.hom.toAlgebra :=
  @AlgHom.comp A P₀.finiteModel P₁.finiteModel P₂.finiteModel _ _ _ _
    P₀.toFinite.hom.toAlgebra P₁.toFinite.hom.toAlgebra
    P₂.toFinite.hom.toAlgebra i₁₂ i₀₁

/-- The canonical morphism of relative dualizing modules induced contravariantly by a
refinement of finite/open presentations. -/
def comparison {A B : CommRingCat.{u}} {phi : A ⟶ B} (P Q : Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom)
    (i : @AlgHom A P.finiteModel Q.finiteModel _ _ _
      P.toFinite.hom.toAlgebra Q.toFinite.hom.toAlgebra)
    (htriangle : Q.toTarget.hom.comp (refinementRingHom P Q i) = P.toTarget.hom) :
    Q.module hA hB h ⟶ P.module hA hB h :=
  @RelativeDualizingModule.comparison A P.finiteModel Q.finiteModel B _ _ _ _ hA hB
    P.toFinite.hom.toAlgebra P.toTarget.hom.toAlgebra phi.hom.toAlgebra P.isScalarTower
    Q.toFinite.hom.toAlgebra Q.toTarget.hom.toAlgebra Q.isScalarTower
    (P.quasiFinite h) P.finite Q.finite P.openImmersion Q.openImmersion
    i htriangle

/-- Comparison morphisms compose contravariantly along successive refinements. -/
theorem comparison_comp {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P₀ P₁ P₂ : Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom)
    (i₀₁ : @AlgHom A P₀.finiteModel P₁.finiteModel _ _ _
      P₀.toFinite.hom.toAlgebra P₁.toFinite.hom.toAlgebra)
    (i₁₂ : @AlgHom A P₁.finiteModel P₂.finiteModel _ _ _
      P₁.toFinite.hom.toAlgebra P₂.toFinite.hom.toAlgebra)
    (htriangle₀₁ : P₁.toTarget.hom.comp (refinementRingHom P₀ P₁ i₀₁) =
      P₀.toTarget.hom)
    (htriangle₁₂ : P₂.toTarget.hom.comp (refinementRingHom P₁ P₂ i₁₂) =
      P₁.toTarget.hom)
    (htriangle₀₂ : P₂.toTarget.hom.comp
      (refinementRingHom P₀ P₂ (refinementComp P₀ P₁ P₂ i₀₁ i₁₂)) =
      P₀.toTarget.hom) :
    comparison P₀ P₂ hA hB h (refinementComp P₀ P₁ P₂ i₀₁ i₁₂) htriangle₀₂ =
      comparison P₁ P₂ hA hB h i₁₂ htriangle₁₂ ≫
        comparison P₀ P₁ hA hB h i₀₁ htriangle₀₁ := sorry

end Presentation

end Algebra.RelativeDualizingModule
