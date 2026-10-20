module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.QuasiCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Realization

/-!
# Twist algebras on relative projective spectra

This module records transition data for gluing the integral twists on affine projective
spectra, together with the graded algebra map and affine comparison data on a realization.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjTwist

section AlgebraMaps

variable {S : Scheme.{u}}

/-- The affine-chart map on sections obtained by pulling back an absolute twist section and
then applying the chosen comparison with the restricted relative twist. -/
noncomputable abbrev sectionComparison
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    {X : Scheme.{u}} {π : X ⟶ S}
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf)
    (U : S.affineOpens) (n : ℕ)
    (localSchemeIso : (π ⁻¹ᵁ (U : S.Opens)).toScheme ≅ Proj (sectionGrading U))
    (localTwistIso :
      (Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist (Int.ofNat n)) ≅
        Scheme.Modules.restrict
          (twistAlgebra (Int.ofNat n)) (π ⁻¹ᵁ (U : S.Opens)).ι)
    (x : Γ((P U).actualTwist (Int.ofNat n), ⊤)) :
    Γ((Scheme.Modules.pushforward π).obj (twistAlgebra (Int.ofNat n)), (U : S.Opens)) :=
  Eq.mp
    (congrArg (fun V : X.Opens ↦ (Γ(twistAlgebra (Int.ofNat n), V) : Type u)) (by simp))
    ((Scheme.Modules.restrictAppIso
        (π ⁻¹ᵁ (U : S.Opens)).ι (twistAlgebra (Int.ofNat n)) ⊤).hom
      ((Scheme.Modules.globalSectionsMap localTwistIso.hom).hom
        ((Scheme.Modules.globalSectionsPullback localSchemeIso.hom
          ((P U).actualTwist (Int.ofNat n))).hom x)))

/-- Multiplication on nonnegative homogeneous sections of an integral graded algebra sheaf. -/
abbrev natMul {X : Scheme.{u}} (ℬ : GradedAlgebraSheaf.{u, u} X.sheaf)
    (U : X.Opens) (i j : ℕ) :
    Γ(ℬ (Int.ofNat i), U) → Γ(ℬ (Int.ofNat j), U) → Γ(ℬ (Int.ofNat (i + j)), U) :=
  fun x y ↦
    Eq.mp
      (congrArg (fun z : ℤ ↦ (Γ(ℬ z, U) : Type u)) (Int.natCast_add i j).symm)
      (ℬ.mul (Opposite.op U) (Int.ofNat i) (Int.ofNat j) x y)

/-- The degree-zero unit of a graded algebra sheaf, regarded as a section of its pushforward. -/
abbrev pushforwardOne {X : Scheme.{u}} (π : X ⟶ S)
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf) (U : S.Opens) :
    Γ((Scheme.Modules.pushforward π).obj (twistAlgebra 0), U) :=
  twistAlgebra.one (Opposite.op (π ⁻¹ᵁ U))

/-- Multiplication on the nonnegative pieces of a pushed-forward integral graded algebra sheaf. -/
abbrev pushforwardMul {X : Scheme.{u}} (π : X ⟶ S)
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf) (U : S.Opens) (i j : ℕ) :
    Γ((Scheme.Modules.pushforward π).obj (twistAlgebra (Int.ofNat i)), U) →
      Γ((Scheme.Modules.pushforward π).obj (twistAlgebra (Int.ofNat j)), U) →
        Γ((Scheme.Modules.pushforward π).obj (twistAlgebra (Int.ofNat (i + j))), U) :=
  natMul twistAlgebra (π ⁻¹ᵁ U) i j

/-- A multiplicative degreewise map from the nonnegative pieces of a graded algebra sheaf to
the pushforwards of an integral graded algebra sheaf. -/
structure Hom (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
    {X : Scheme.{u}} (π : X ⟶ S)
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf) where
  /-- The map on each nonnegative homogeneous piece. -/
  hom : ∀ n : ℕ, 𝒜 (Int.ofNat n) ⟶
    (Scheme.Modules.pushforward π).obj (twistAlgebra (Int.ofNat n))
  /-- The degree-zero component preserves the unit. -/
  map_one : ∀ U : S.Opens,
    (Scheme.Modules.Hom.app (hom 0) U).hom (𝒜.one (Opposite.op U)) =
      pushforwardOne π twistAlgebra U
  /-- The homogeneous components preserve multiplication. -/
  map_mul : ∀ (U : S.Opens) (i j : ℕ)
      (x : Γ(𝒜 (Int.ofNat i), U)) (y : Γ(𝒜 (Int.ofNat j), U)),
    (Scheme.Modules.Hom.app (hom (i + j)) U).hom (natMul 𝒜 U i j x y) =
      pushforwardMul π twistAlgebra U i j
        ((Scheme.Modules.Hom.app (hom i) U).hom x)
        ((Scheme.Modules.Hom.app (hom j) U).hom y)

namespace Hom

/-- Construct a multiplicative relative-projective twist map from its components and laws. -/
def ofComponents {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
    {X : Scheme.{u}} {π : X ⟶ S}
    {twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf}
    (hom : ∀ n : ℕ, 𝒜 (Int.ofNat n) ⟶
      (Scheme.Modules.pushforward π).obj (twistAlgebra (Int.ofNat n)))
    (map_one : ∀ U : S.Opens,
      (Scheme.Modules.Hom.app (hom 0) U).hom (𝒜.one (Opposite.op U)) =
        pushforwardOne π twistAlgebra U)
    (map_mul : ∀ (U : S.Opens) (i j : ℕ)
        (x : Γ(𝒜 (Int.ofNat i), U)) (y : Γ(𝒜 (Int.ofNat j), U)),
      (Scheme.Modules.Hom.app (hom (i + j)) U).hom (natMul 𝒜 U i j x y) =
        pushforwardMul π twistAlgebra U i j
          ((Scheme.Modules.Hom.app (hom i) U).hom x)
          ((Scheme.Modules.Hom.app (hom j) U).hom y)) :
    Hom 𝒜 π twistAlgebra where
  hom := hom
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication laws of a relative-projective twist map. -/
theorem spec {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
    {X : Scheme.{u}} {π : X ⟶ S}
    {twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf}
    (ψ : Hom 𝒜 π twistAlgebra) :
    (∀ U : S.Opens,
      (Scheme.Modules.Hom.app (ψ.hom 0) U).hom (𝒜.one (Opposite.op U)) =
        pushforwardOne π twistAlgebra U) ∧
    ∀ (U : S.Opens) (i j : ℕ)
        (x : Γ(𝒜 (Int.ofNat i), U)) (y : Γ(𝒜 (Int.ofNat j), U)),
      (Scheme.Modules.Hom.app (ψ.hom (i + j)) U).hom (natMul 𝒜 U i j x y) =
        pushforwardMul π twistAlgebra U i j
          ((Scheme.Modules.Hom.app (ψ.hom i) U).hom x)
          ((Scheme.Modules.Hom.app (ψ.hom j) U).hom y) :=
  ⟨ψ.map_one, ψ.map_mul⟩

/-- Two relative-projective twist maps are equal when all their homogeneous components agree. -/
@[ext]
theorem ext {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
    {X : Scheme.{u}} {π : X ⟶ S}
    {twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf}
    (f g : Hom 𝒜 π twistAlgebra) (h : ∀ n : ℕ, f.hom n = g.hom n) : f = g := sorry

end Hom

/-- The degree-zero unit of a relative twist algebra restricted to an affine chart. -/
abbrev restrictedOne {X : Scheme.{u}} (π : X ⟶ S)
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf)
    (U : S.affineOpens) (V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ) :
    Γ(Scheme.Modules.restrict (twistAlgebra 0) (π ⁻¹ᵁ (U : S.Opens)).ι, V.unop) :=
  (Scheme.Modules.restrictAppIso
      (π ⁻¹ᵁ (U : S.Opens)).ι (twistAlgebra 0) V.unop).inv
    (twistAlgebra.one
      (Opposite.op (((π ⁻¹ᵁ (U : S.Opens)).ι) ''ᵁ V.unop)))

/-- Multiplication of relative twists after restriction to an affine chart. -/
abbrev restrictedMul {X : Scheme.{u}} (π : X ⟶ S)
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf)
    (U : S.affineOpens) (V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ) (a b : ℤ) :
    Γ(Scheme.Modules.restrict (twistAlgebra a) (π ⁻¹ᵁ (U : S.Opens)).ι, V.unop) →
      Γ(Scheme.Modules.restrict (twistAlgebra b) (π ⁻¹ᵁ (U : S.Opens)).ι, V.unop) →
        Γ(Scheme.Modules.restrict (twistAlgebra (a + b))
          (π ⁻¹ᵁ (U : S.Opens)).ι, V.unop) :=
  fun x y ↦
    (Scheme.Modules.restrictAppIso
        (π ⁻¹ᵁ (U : S.Opens)).ι (twistAlgebra (a + b)) V.unop).inv
      (twistAlgebra.mul
        (Opposite.op (((π ⁻¹ᵁ (U : S.Opens)).ι) ''ᵁ V.unop)) a b
        ((Scheme.Modules.restrictAppIso
            (π ⁻¹ᵁ (U : S.Opens)).ι (twistAlgebra a) V.unop).hom x)
        ((Scheme.Modules.restrictAppIso
            (π ⁻¹ᵁ (U : S.Opens)).ι (twistAlgebra b) V.unop).hom y))

/-- A degreewise affine-chart identification between absolute twists and restricted relative
twists that preserves the graded-algebra unit and multiplication. -/
structure ChartComparison
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    {X : Scheme.{u}} (π : X ⟶ S)
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf)
    (U : S.affineOpens)
    (localSchemeIso : (π ⁻¹ᵁ (U : S.Opens)).toScheme ≅ Proj (sectionGrading U)) where
  /-- The comparison in every integral degree. -/
  iso : ∀ n : ℤ,
    (Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist n) ≅
      Scheme.Modules.restrict (twistAlgebra n) (π ⁻¹ᵁ (U : S.Opens)).ι
  /-- The degree-zero comparison preserves the unit. -/
  map_one : ∀ V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ,
    ((((iso 0).hom).app V.unop).hom) ((P U).actualOne localSchemeIso.hom V) =
      restrictedOne π twistAlgebra U V
  /-- The comparisons preserve multiplication in all integral degrees. -/
  map_mul : ∀ (V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ) (a b : ℤ)
      (x : Γ((Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist a), V.unop))
      (y : Γ((Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist b), V.unop)),
    ((((iso (a + b)).hom).app V.unop).hom) ((P U).actualMul localSchemeIso.hom V a b x y) =
      restrictedMul π twistAlgebra U V a b
        ((((iso a).hom).app V.unop).hom x)
        ((((iso b).hom).app V.unop).hom y)

namespace ChartComparison

/-- Construct an affine-chart comparison from degreewise isomorphisms and their algebra laws. -/
def ofComponents
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {X : Scheme.{u}} {π : X ⟶ S}
    {twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf}
    {U : S.affineOpens}
    {localSchemeIso : (π ⁻¹ᵁ (U : S.Opens)).toScheme ≅ Proj (sectionGrading U)}
    (iso : ∀ n : ℤ,
      (Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist n) ≅
        Scheme.Modules.restrict (twistAlgebra n) (π ⁻¹ᵁ (U : S.Opens)).ι)
    (map_one : ∀ V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ,
      ((((iso 0).hom).app V.unop).hom) ((P U).actualOne localSchemeIso.hom V) =
        restrictedOne π twistAlgebra U V)
    (map_mul : ∀ (V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ) (a b : ℤ)
        (x : Γ((Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist a), V.unop))
        (y : Γ((Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist b), V.unop)),
      ((((iso (a + b)).hom).app V.unop).hom) ((P U).actualMul localSchemeIso.hom V a b x y) =
        restrictedMul π twistAlgebra U V a b
          ((((iso a).hom).app V.unop).hom x)
          ((((iso b).hom).app V.unop).hom y)) :
    ChartComparison sectionGrading P π twistAlgebra U localSchemeIso where
  iso := iso
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication laws carried by an affine-chart comparison. -/
theorem spec
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {X : Scheme.{u}} {π : X ⟶ S}
    {twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf}
    {U : S.affineOpens}
    {localSchemeIso : (π ⁻¹ᵁ (U : S.Opens)).toScheme ≅ Proj (sectionGrading U)}
    (c : ChartComparison sectionGrading P π twistAlgebra U localSchemeIso) :
    (∀ V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ,
      ((((c.iso 0).hom).app V.unop).hom) ((P U).actualOne localSchemeIso.hom V) =
        restrictedOne π twistAlgebra U V) ∧
    ∀ (V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ) (a b : ℤ)
        (x : Γ((Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist a), V.unop))
        (y : Γ((Scheme.Modules.pullback localSchemeIso.hom).obj ((P U).actualTwist b), V.unop)),
      ((((c.iso (a + b)).hom).app V.unop).hom) ((P U).actualMul localSchemeIso.hom V a b x y) =
        restrictedMul π twistAlgebra U V a b
          ((((c.iso a).hom).app V.unop).hom x)
          ((((c.iso b).hom).app V.unop).hom y) :=
  ⟨c.map_one, c.map_mul⟩

end ChartComparison

end AlgebraMaps

section TransitionData

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf ℤ) [𝒜.IsCommutative]
variable (hqc : 𝒜.IsQuasicoherent)
variable (A σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (model : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
variable (hModel : ∀ U : S.affineOpens,
  AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
  (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
    (d : ℕ) (x : sectionGrading U' d),
    model U d
        ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom) ((model U' d).symm x)) =
      (sectionRestrict h).gradedAddHom d x)

/-- Explicit integral-twist transition isomorphisms for the affine pieces of a relative
projective spectrum, faithful to the canonical transition morphisms and their cocycle. -/
structure TransitionSystem where
  /-- The transition isomorphism for every inclusion of affine opens and every integral degree. -/
  theta : ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens)) (n : ℤ),
    (Scheme.Modules.pullback
      ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
        sectionRestrict sectionRestrict_spec).rho h)).obj ((P U').actualTwist n) ≅
      (P U).actualTwist n
  /-- Each chosen isomorphism has the canonical transported theta morphism as its forward map. -/
  theta_hom : ∀ ⦃U U' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens)) (n : ℤ),
    (theta h n).hom =
      let hTop := AffineOpenSectionProj.domain_eq_top
        (sectionGrading U) (sectionGrading U') h 𝒜 hqc
        (model U) (model U') (hModel U) (hModel U')
        (sectionRestrict h) (sectionRestrict_spec h)
      projMapThetaOnTarget (sectionRestrict h)
        ((P U').actualTwist n) ((P U).actualTwist n)
        (projMap (P U') (P U) (sectionRestrict h)).map
        ((projMap (P U') (P U) (sectionRestrict h)).theta n) hTop
        (projMapDomainTopInclusion_comp_ι (sectionRestrict h) hTop)
  /-- The transition isomorphisms compose along nested affine inclusions. -/
  theta_cocycle : ∀ ⦃U U' U'' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens))
      (h' : (U' : S.Opens) ≤ (U'' : S.Opens)) (n : ℤ),
    ((Scheme.Modules.pullbackCongr
      ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
        sectionRestrict sectionRestrict_spec).cocycle h h')).hom.app
          ((P U'').actualTwist n)) ≫
      ((Scheme.Modules.pullbackComp
        ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
          sectionRestrict sectionRestrict_spec).rho h)
        ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
          sectionRestrict sectionRestrict_spec).rho h')).inv.app
            ((P U'').actualTwist n)) ≫
      (Scheme.Modules.pullback
        ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
          sectionRestrict sectionRestrict_spec).rho h)).map (theta h' n).hom ≫
      (theta h n).hom = (theta (h.trans h') n).hom

namespace TransitionSystem

/-- Construct faithful twist-transition data from explicitly supplied isomorphisms and laws. -/
def ofComponents
    (theta : ∀ ⦃U U' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens)) (n : ℤ),
      (Scheme.Modules.pullback
        ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
          sectionRestrict sectionRestrict_spec).rho h)).obj ((P U').actualTwist n) ≅
        (P U).actualTwist n)
    (theta_hom : ∀ ⦃U U' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens)) (n : ℤ),
      (theta h n).hom =
        let hTop := AffineOpenSectionProj.domain_eq_top
          (sectionGrading U) (sectionGrading U') h 𝒜 hqc
          (model U) (model U') (hModel U) (hModel U')
          (sectionRestrict h) (sectionRestrict_spec h)
        projMapThetaOnTarget (sectionRestrict h)
          ((P U').actualTwist n) ((P U).actualTwist n)
          (projMap (P U') (P U) (sectionRestrict h)).map
          ((projMap (P U') (P U) (sectionRestrict h)).theta n) hTop
          (projMapDomainTopInclusion_comp_ι (sectionRestrict h) hTop))
    (theta_cocycle : ∀ ⦃U U' U'' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens))
      (h' : (U' : S.Opens) ≤ (U'' : S.Opens)) (n : ℤ),
      ((Scheme.Modules.pullbackCongr
        ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
          sectionRestrict sectionRestrict_spec).cocycle h h')).hom.app
            ((P U'').actualTwist n)) ≫
        ((Scheme.Modules.pullbackComp
          ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
            sectionRestrict sectionRestrict_spec).rho h)
          ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
            sectionRestrict sectionRestrict_spec).rho h')).inv.app
              ((P U'').actualTwist n)) ≫
        (Scheme.Modules.pullback
          ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
            sectionRestrict sectionRestrict_spec).rho h)).map (theta h' n).hom ≫
        (theta h n).hom = (theta (h.trans h') n).hom) :
    TransitionSystem 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec where
  theta := theta
  theta_hom := theta_hom
  theta_cocycle := theta_cocycle

/-- Faithfulness to the canonical theta maps and the cocycle law of a transition system. -/
theorem spec
    (T : TransitionSystem 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec) :
    (∀ ⦃U U' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens)) (n : ℤ),
      (T.theta h n).hom =
        let hTop := AffineOpenSectionProj.domain_eq_top
          (sectionGrading U) (sectionGrading U') h 𝒜 hqc
          (model U) (model U') (hModel U) (hModel U')
          (sectionRestrict h) (sectionRestrict_spec h)
        projMapThetaOnTarget (sectionRestrict h)
          ((P U').actualTwist n) ((P U).actualTwist n)
          (projMap (P U') (P U) (sectionRestrict h)).map
          ((projMap (P U') (P U) (sectionRestrict h)).theta n) hTop
          (projMapDomainTopInclusion_comp_ι (sectionRestrict h) hTop)) ∧
    ∀ ⦃U U' U'' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens))
      (h' : (U' : S.Opens) ≤ (U'' : S.Opens)) (n : ℤ),
      ((Scheme.Modules.pullbackCongr
        ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
          sectionRestrict sectionRestrict_spec).cocycle h h')).hom.app
            ((P U'').actualTwist n)) ≫
        ((Scheme.Modules.pullbackComp
          ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
            sectionRestrict sectionRestrict_spec).rho h)
          ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
            sectionRestrict sectionRestrict_spec).rho h')).inv.app
              ((P U'').actualTwist n)) ≫
        (Scheme.Modules.pullback
          ((relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
            sectionRestrict sectionRestrict_spec).rho h)).map (T.theta h' n).hom ≫
        (T.theta h n).hom = (T.theta (h.trans h') n).hom :=
  ⟨T.theta_hom, T.theta_cocycle⟩

end TransitionSystem

/-- The basis-indexed quasi-coherent gluing datum for one integral twist degree. -/
def gluingData
    (T : TransitionSystem 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec) (n : ℤ) :
    Scheme.Modules.BasisQuasiCoherentGluing.{u, u} S :=
  Scheme.Modules.BasisQuasiCoherentGluing.ofBasisSchemeGluing
    (relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec)
    (fun U ↦ (P U).actualTwist n)
    (fun U ↦ (P U).twistAlgebra.isQuasicoherent n)
    (fun {_ _} h ↦ T.theta h n)
    (fun {_ _ _} h h' ↦ T.theta_cocycle h h' n)

/-- The local modules and transition maps of the integral-twist gluing datum are the prescribed
absolute twists and the canonical transported theta maps. -/
theorem gluingData_spec
    (T : TransitionSystem 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec) (n : ℤ) :
    (∀ U : S.affineOpens,
      (gluingData 𝒜 hqc A σ sectionGrading model hModel P
        sectionRestrict sectionRestrict_spec T n).F U = (P U).actualTwist n) ∧
    ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens)),
      ((gluingData 𝒜 hqc A σ sectionGrading model hModel P
        sectionRestrict sectionRestrict_spec T n).theta h).hom =
        let hTop := AffineOpenSectionProj.domain_eq_top
          (sectionGrading U) (sectionGrading U') h 𝒜 hqc
          (model U) (model U') (hModel U) (hModel U')
          (sectionRestrict h) (sectionRestrict_spec h)
        projMapThetaOnTarget (sectionRestrict h)
          ((P U').actualTwist n) ((P U).actualTwist n)
          (projMap (P U') (P U) (sectionRestrict h)).map
          ((projMap (P U') (P U) (sectionRestrict h)).theta n) hTop
          (projMapDomainTopInclusion_comp_ι (sectionRestrict h) hTop) :=
  ⟨fun _ ↦ rfl, fun {_ _} h ↦ T.theta_hom h n⟩

end TransitionData

section Presentations

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
variable (A σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (model : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)

/-- A relative-projective twist algebra, its multiplicative map, and compatible affine-chart
identifications satisfying the defining section diagrams. -/
structure Presentation {X : Scheme.{u}} (π : X ⟶ S) where
  /-- The integral graded algebra sheaf of relative twists. -/
  twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf
  /-- Every integral twist is quasi-coherent. -/
  twist_isQuasicoherent : ∀ n : ℤ, (twistAlgebra n).IsQuasicoherent
  /-- The multiplicative map from the nonnegative pieces of the original graded algebra. -/
  psi : Hom 𝒜 π twistAlgebra
  /-- The chosen affine projective-spectrum chart over every affine open of the base. -/
  localSchemeIso :
    ∀ U : S.affineOpens, (π ⁻¹ᵁ (U : S.Opens)).toScheme ≅ Proj (sectionGrading U)
  /-- The graded-algebra comparison on every affine chart. -/
  localTwistComparison : ∀ U : S.affineOpens,
    ChartComparison sectionGrading P π twistAlgebra U (localSchemeIso U)
  /-- The global map agrees with the absolute section map in every affine chart and degree. -/
  psi_commutes : ∀ (U : S.affineOpens) (n : ℕ)
      (x : Γ(𝒜 (Int.ofNat n), (U : S.Opens))),
    (Scheme.Modules.Hom.app (psi.hom n) (U : S.Opens)).hom x =
      sectionComparison sectionGrading P twistAlgebra U n (localSchemeIso U)
        ((localTwistComparison U).iso (Int.ofNat n))
        ((AddCommGrpCat.Hom.hom ((P U).actualSectionMap n)) (model U n x))

namespace Presentation

/-- Construct a relative-projective twist presentation from its global and affine-local data. -/
def ofComponents
    {X : Scheme.{u}} {π : X ⟶ S}
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf)
    (twist_isQuasicoherent : ∀ n : ℤ, (twistAlgebra n).IsQuasicoherent)
    (psi : Hom 𝒜 π twistAlgebra)
    (localSchemeIso :
      ∀ U : S.affineOpens, (π ⁻¹ᵁ (U : S.Opens)).toScheme ≅ Proj (sectionGrading U))
    (localTwistComparison : ∀ U : S.affineOpens,
      ChartComparison sectionGrading P π twistAlgebra U (localSchemeIso U))
    (psi_commutes : ∀ (U : S.affineOpens) (n : ℕ)
        (x : Γ(𝒜 (Int.ofNat n), (U : S.Opens))),
      (Scheme.Modules.Hom.app (psi.hom n) (U : S.Opens)).hom x =
        sectionComparison sectionGrading P twistAlgebra U n (localSchemeIso U)
          ((localTwistComparison U).iso (Int.ofNat n))
          ((AddCommGrpCat.Hom.hom ((P U).actualSectionMap n)) (model U n x))) :
    Presentation 𝒜 A σ sectionGrading P model π where
  twistAlgebra := twistAlgebra
  twist_isQuasicoherent := twist_isQuasicoherent
  psi := psi
  localSchemeIso := localSchemeIso
  localTwistComparison := localTwistComparison
  psi_commutes := psi_commutes

/-- A presentation exposes quasi-coherence, the affine graded-algebra comparison laws, and all
of its defining affine section diagrams. -/
theorem spec {X : Scheme.{u}} {π : X ⟶ S}
    (presentation : Presentation 𝒜 A σ sectionGrading P model π) :
    (∀ n : ℤ, (presentation.twistAlgebra n).IsQuasicoherent) ∧
    (∀ (U : S.affineOpens)
        (V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ),
      (((((presentation.localTwistComparison U).iso 0).hom).app V.unop).hom)
          ((P U).actualOne (presentation.localSchemeIso U).hom V) =
        restrictedOne π presentation.twistAlgebra U V) ∧
    (∀ (U : S.affineOpens)
        (V : ((π ⁻¹ᵁ (U : S.Opens)).toScheme.Opens)ᵒᵖ) (a b : ℤ)
        (x : Γ((Scheme.Modules.pullback (presentation.localSchemeIso U).hom).obj
          ((P U).actualTwist a), V.unop))
        (y : Γ((Scheme.Modules.pullback (presentation.localSchemeIso U).hom).obj
          ((P U).actualTwist b), V.unop)),
      (((((presentation.localTwistComparison U).iso (a + b)).hom).app V.unop).hom)
          ((P U).actualMul (presentation.localSchemeIso U).hom V a b x y) =
        restrictedMul π presentation.twistAlgebra U V a b
          (((((presentation.localTwistComparison U).iso a).hom).app V.unop).hom x)
          (((((presentation.localTwistComparison U).iso b).hom).app V.unop).hom y)) ∧
    ∀ (U : S.affineOpens) (n : ℕ)
        (x : Γ(𝒜 (Int.ofNat n), (U : S.Opens))),
      (Scheme.Modules.Hom.app (presentation.psi.hom n) (U : S.Opens)).hom x =
        sectionComparison sectionGrading P presentation.twistAlgebra U n
          (presentation.localSchemeIso U)
          ((presentation.localTwistComparison U).iso (Int.ofNat n))
          ((AddCommGrpCat.Hom.hom ((P U).actualSectionMap n)) (model U n x)) :=
  ⟨presentation.twist_isQuasicoherent,
    fun U ↦ (presentation.localTwistComparison U).map_one,
    fun U ↦ (presentation.localTwistComparison U).map_mul,
    presentation.psi_commutes⟩

end Presentation

/-- A candidate multiplicative map has the prescribed absolute section maps relative to fixed
affine-chart comparisons. -/
def HomCompatibility
    {X : Scheme.{u}} (π : X ⟶ S)
    (twistAlgebra : GradedAlgebraSheaf.{u, u} X.sheaf)
    (localSchemeIso :
      ∀ U : S.affineOpens, (π ⁻¹ᵁ (U : S.Opens)).toScheme ≅ Proj (sectionGrading U))
    (localTwistComparison : ∀ U : S.affineOpens,
      ChartComparison sectionGrading P π twistAlgebra U (localSchemeIso U))
    (ψ : Hom 𝒜 π twistAlgebra) : Prop :=
  ∀ (U : S.affineOpens) (n : ℕ)
      (x : Γ(𝒜 (Int.ofNat n), (U : S.Opens))),
    (Scheme.Modules.Hom.app (ψ.hom n) (U : S.Opens)).hom x =
      sectionComparison sectionGrading P twistAlgebra U n (localSchemeIso U)
        ((localTwistComparison U).iso (Int.ofNat n))
        ((AddCommGrpCat.Hom.hom ((P U).actualSectionMap n)) (model U n x))

namespace Hom

/-- A compatible multiplicative map into the twist algebra of a presentation is uniquely the
map carried by that presentation. -/
theorem unique
    {X : Scheme.{u}} {π : X ⟶ S}
    (presentation : Presentation 𝒜 A σ sectionGrading P model π)
    {ψ' : Hom 𝒜 π presentation.twistAlgebra}
    (hψ' : HomCompatibility 𝒜 A σ sectionGrading P model
      π presentation.twistAlgebra presentation.localSchemeIso
        presentation.localTwistComparison ψ') :
    ψ' = presentation.psi := sorry

end Hom

end Presentations

section Existence

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf ℤ) [𝒜.IsCommutative]
variable (hqc : 𝒜.IsQuasicoherent)
variable (A σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (model : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
variable (hModel : ∀ U : S.affineOpens,
  AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
  (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
    (d : ℕ) (x : sectionGrading U' d),
    model U d
        ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom) ((model U' d).symm x)) =
      (sectionRestrict h).gradedAddHom d x)

/-- An equipped realization of relative projective spectrum admits a quasi-coherent integral
twist algebra and its uniquely determined compatible multiplicative section map. -/
theorem existsPresentation
    (R : (relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec).Realization) :
    ∃ presentation : Presentation 𝒜 A σ sectionGrading P
        (fun U d ↦ (model U d).toEquiv) R.toBase,
      (∀ U : S.affineOpens, presentation.localSchemeIso U = R.localIso U) ∧
      ∀ (ψ' : Hom 𝒜 R.toBase presentation.twistAlgebra),
        HomCompatibility 𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv)
          R.toBase presentation.twistAlgebra presentation.localSchemeIso
            presentation.localTwistComparison ψ' →
          ψ' = presentation.psi := sorry

end Existence

end AlgebraicGeometry.Scheme.RelativeProjTwist
