/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion
import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.TensorProductBaseChange

/-!
# Affine-open base change for projective spectra

This file relates projective spectra of graded rings modelling the sections of a
quasi-coherent graded algebra sheaf on nested affine opens.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

section TwistTransport

variable {A sigma : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
variable {calA : Nat -> sigma} [GradedRing calA]

namespace ProjTwistPresentation

/-- Multiplication on the actual twists over a projective spectrum, transported through the
canonical identification of pullback along the identity. -/
noncomputable def mulOnSelf
    (P : ProjTwistPresentation calA)
    (W : ((Proj calA).Opens)ᵒᵖ) (a b : ℤ) :
    (P.actualTwist a).val.obj W →
      (P.actualTwist b).val.obj W →
        (P.actualTwist (a + b)).val.obj W :=
  fun x y ↦
    ((((Scheme.Modules.pullbackId (Proj calA)).hom.app
        (P.actualTwist (a + b))).val.app W).hom)
      (P.actualMul (𝟙 (Proj calA)) W a b
        ((((Scheme.Modules.pullbackId (Proj calA)).inv.app
            (P.actualTwist a)).val.app W).hom x)
        ((((Scheme.Modules.pullbackId (Proj calA)).inv.app
            (P.actualTwist b)).val.app W).hom y))

end ProjTwistPresentation

end TwistTransport

section MapTransport

variable {A B sigma tau : Type u}
variable [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
variable [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
variable {calA : Nat -> sigma} {calB : Nat -> tau} [GradedRing calA] [GradedRing calB]
variable {PcalA : ProjTwistPresentation calA} {PcalB : ProjTwistPresentation calB}
variable {psi : calA →+*ᵍ calB}

namespace ProjMap

/-- A comparison family on a full projective-spectrum map is compatible with multiplication
when it carries multiplication on pulled-back source twists to multiplication on target twists. -/
abbrev ThetaOnTargetMulCompatible
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation calB)
    (r : Proj calB ⟶ Proj calA)
    (theta : ∀ n : ℤ,
      (Scheme.Modules.pullback r).obj (PcalA.actualTwist n) ⟶ PcalB.actualTwist n) : Prop :=
  ∀ (W : ((Proj calB).Opens)ᵒᵖ) (a b : ℤ)
    (x : ((Scheme.Modules.pullback r).obj (PcalA.actualTwist a)).val.obj W)
    (y : ((Scheme.Modules.pullback r).obj (PcalA.actualTwist b)).val.obj W),
    (((theta (a + b)).val.app W).hom) (PcalA.actualMul r W a b x y) =
      PcalB.mulOnSelf W a b
        ((((theta a).val.app W).hom) x)
        ((((theta b).val.app W).hom) y)

/-- Transporting the theta family of a projective-spectrum map from a top natural domain to the
full target preserves multiplication. -/
theorem thetaOnTarget_mul
    (hProj : ProjMap PcalA PcalB psi)
    (hTop : projMapDomain psi = ⊤) :
    ThetaOnTargetMulCompatible PcalA PcalB
      (projMapOnTarget psi hProj.map hTop)
      (fun n ↦ projMapThetaOnTarget psi (PcalA.actualTwist n) (PcalB.actualTwist n)
        hProj.map (hProj.theta n) hTop (projMapDomainTopInclusion_comp_ι psi hTop)) := sorry

end ProjMap

end MapTransport

namespace AffineOpenSectionProj

section

variable {S : Scheme.{u}}
variable {U U' : S.affineOpens}
variable {A A' sigma tau : Type u}
variable [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
variable [CommRing A'] [SetLike tau A'] [AddSubgroupClass tau A']
variable (calA : ℕ → sigma) [GradedRing calA]
variable (calA' : ℕ → tau) [GradedRing calA']

/-- Degreewise additive identifications between affine-open sections of a graded algebra sheaf
and a graded ring model preserve the degree-zero unit and all homogeneous products. -/
abbrev IsAffineOpenSectionModel
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (U : S.affineOpens)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d) : Prop :=
  model 0 (𝒜.one (Opposite.op (U : S.Opens))) =
      (1 : calA 0) ∧
    ∀ (d e : ℕ)
      (x : (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)))
      (y : (𝒜.obj (Int.ofNat e)).val.obj (Opposite.op (U : S.Opens))),
      HEq
        (𝒜.mul (Opposite.op (U : S.Opens)) (Int.ofNat d) (Int.ofNat e) x y)
        ((model (d + e)).symm
          ((SetLike.gMul calA).mul (model d x) (model e y)))

/-- A compatible affine-open section model carries the sheaf unit to the graded unit. -/
theorem IsAffineOpenSectionModel.one_eq
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (U : S.affineOpens)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model) :
    model 0 (𝒜.one (Opposite.op (U : S.Opens))) =
      (1 : calA 0) :=
  hModel.1

/-- A compatible affine-open section model carries homogeneous sheaf multiplication to the
graded multiplication of its model. -/
theorem IsAffineOpenSectionModel.mul_eq
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (U : S.affineOpens)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model)
    (d e : ℕ)
    (x : (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)))
    (y : (𝒜.obj (Int.ofNat e)).val.obj (Opposite.op (U : S.Opens))) :
    HEq
      (𝒜.mul (Opposite.op (U : S.Opens)) (Int.ofNat d) (Int.ofNat e) x y)
      ((model (d + e)).symm
        ((SetLike.gMul calA).mul (model d x) (model e y))) :=
  hModel.2 d e x y

/-- The scalar action on the chosen degree-zero unit satisfies the ring-homomorphism laws after
transport to an affine-open graded-ring model. -/
theorem degreeZeroStructureMap_spec
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (U : S.affineOpens)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model) :
    let f := fun r : S.presheaf.obj (Opposite.op (U : S.Opens)) ↦
      model 0 (r • 𝒜.one (Opposite.op (U : S.Opens)))
    f 0 = 0 ∧ f 1 = 1 ∧
      (∀ x y, f (x + y) = f x + f y) ∧
        ∀ x y, f (x * y) = f x * f y := sorry

/-- The degree-zero structure homomorphism of an affine-open section model sends a function
`r` to the model of `r • 1`. -/
noncomputable def degreeZeroStructureMap
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (U : S.affineOpens)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model) :
    S.presheaf.obj (Opposite.op (U : S.Opens)) →+* calA 0 where
  toFun r := model 0 (r • 𝒜.one (Opposite.op (U : S.Opens)))
  map_zero' := (degreeZeroStructureMap_spec calA 𝒜 U model hModel).1
  map_one' := (degreeZeroStructureMap_spec calA 𝒜 U model hModel).2.1
  map_add' := (degreeZeroStructureMap_spec calA 𝒜 U model hModel).2.2.1
  map_mul' := (degreeZeroStructureMap_spec calA 𝒜 U model hModel).2.2.2

/-- The structure morphism from the projective spectrum of an affine-open section model to the
affine open is induced by its canonical degree-zero structure homomorphism. -/
noncomputable def toAffineOpen
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (U : S.affineOpens)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model) :
    Proj calA ⟶ (U : S.Opens).toScheme :=
  Proj.toSpecZero calA ≫
    Spec.map (CommRingCat.ofHom (degreeZeroStructureMap calA 𝒜 U model hModel)) ≫
    U.2.isoSpec.inv

/-- Quasi-coherent restriction between nested affine opens gives a graded map whose natural
projective-spectrum domain is the whole source projective spectrum. -/
theorem domain_eq_top
    (h : (U : S.Opens) ≤ (U' : S.Opens))
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (model' : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃+ calA' d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model)
    (hModel' : IsAffineOpenSectionModel calA' 𝒜 U' model')
    (sectionRestrict : calA' →+*ᵍ calA)
    (sectionRestrict_spec :
      ∀ d : ℕ, ∀ x : calA' d,
        model d
            ((((𝒜.obj (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model' d).symm x)) =
          (sectionRestrict.gradedAddHom d) x) :
    projMapDomain sectionRestrict = ⊤ := sorry

/-- For nested affine opens, the projective spectra of compatible section-ring models form a
cartesian square over the corresponding open subschemes. -/
theorem isPullback
    (h : (U : S.Opens) ≤ (U' : S.Opens))
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (model' : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃+ calA' d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model)
    (hModel' : IsAffineOpenSectionModel calA' 𝒜 U' model')
    (PcalA : ProjTwistPresentation calA)
    (PcalA' : ProjTwistPresentation calA')
    (sectionRestrict : calA' →+*ᵍ calA)
    (sectionRestrict_spec :
      ∀ d : ℕ, ∀ x : calA' d,
        model d
            ((((𝒜.obj (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model' d).symm x)) =
          (sectionRestrict.gradedAddHom d) x) :
    let hTop := domain_eq_top calA calA' h 𝒜 hqc model model' hModel hModel'
      sectionRestrict sectionRestrict_spec
    CategoryTheory.IsPullback
      (projMapOnTarget sectionRestrict (projMap PcalA' PcalA sectionRestrict).map hTop)
      (toAffineOpen calA 𝒜 U model hModel)
      (toAffineOpen calA' 𝒜 U' model' hModel')
      (S.homOfLE h) := sorry

/-- For nested affine opens, every transported comparison between corresponding integral twists
on the projective spectra of compatible section-ring models is an isomorphism. -/
theorem theta_isIso
    (h : (U : S.Opens) ≤ (U' : S.Opens))
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (model' : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃+ calA' d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model)
    (hModel' : IsAffineOpenSectionModel calA' 𝒜 U' model')
    (PcalA : ProjTwistPresentation calA)
    (PcalA' : ProjTwistPresentation calA')
    (sectionRestrict : calA' →+*ᵍ calA)
    (sectionRestrict_spec :
      ∀ d : ℕ, ∀ x : calA' d,
        model d
            ((((𝒜.obj (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model' d).symm x)) =
          (sectionRestrict.gradedAddHom d) x)
    (n : ℤ) :
    let hTop := domain_eq_top calA calA' h 𝒜 hqc model model' hModel hModel'
      sectionRestrict sectionRestrict_spec
    IsIso
      (projMapThetaOnTarget sectionRestrict (PcalA'.actualTwist n) (PcalA.actualTwist n)
        (projMap PcalA' PcalA sectionRestrict).map
        ((projMap PcalA' PcalA sectionRestrict).theta n) hTop
        (projMapDomainTopInclusion_comp_ι sectionRestrict hTop)) := sorry

/-- For nested affine opens, the transported comparison family between corresponding integral
twists on compatible section-ring models preserves multiplication. -/
theorem theta_mul
    (h : (U : S.Opens) ≤ (U' : S.Opens))
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
    (model' : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃+ calA' d)
    (hModel : IsAffineOpenSectionModel calA 𝒜 U model)
    (hModel' : IsAffineOpenSectionModel calA' 𝒜 U' model')
    (PcalA : ProjTwistPresentation calA)
    (PcalA' : ProjTwistPresentation calA')
    (sectionRestrict : calA' →+*ᵍ calA)
    (sectionRestrict_spec :
      ∀ d : ℕ, ∀ x : calA' d,
        model d
            ((((𝒜.obj (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model' d).symm x)) =
          (sectionRestrict.gradedAddHom d) x) :
    let hTop := domain_eq_top calA calA' h 𝒜 hqc model model' hModel hModel'
      sectionRestrict sectionRestrict_spec
    ProjMap.ThetaOnTargetMulCompatible PcalA' PcalA
      (projMapOnTarget sectionRestrict (projMap PcalA' PcalA sectionRestrict).map hTop)
      (fun n ↦ projMapThetaOnTarget sectionRestrict
        (PcalA'.actualTwist n) (PcalA.actualTwist n)
        (projMap PcalA' PcalA sectionRestrict).map
        ((projMap PcalA' PcalA sectionRestrict).theta n) hTop
        (projMapDomainTopInclusion_comp_ι sectionRestrict hTop)) :=
  ProjMap.thetaOnTarget_mul (projMap PcalA' PcalA sectionRestrict)
    (domain_eq_top calA calA' h 𝒜 hqc model model' hModel hModel'
      sectionRestrict sectionRestrict_spec)

end

end AffineOpenSectionProj

end AlgebraicGeometry
