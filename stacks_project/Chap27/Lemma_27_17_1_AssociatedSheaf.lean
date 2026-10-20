/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Module
public import stacks_project.Chap27.Lemma_27_15_5

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.GradedModuleSheaf

variable {S : Scheme.{u}}

/-- Degreewise quasi-coherent graded modules over a graded algebra on a scheme. -/
abbrev isQuasicoherent
    (A : GradedAlgebraSheaf.{u, u} S.sheaf) :
    ObjectProperty (_root_.SheafOfModules.RingedSite.GradedModuleSheaf.{u, u} A) :=
  fun M ↦ ∀ n : ℤ, (M n).IsQuasicoherent

/-- Membership in `isQuasicoherent A` means quasi-coherence in every degree. -/
theorem isQuasicoherent_iff (A : GradedAlgebraSheaf.{u, u} S.sheaf)
    (M : _root_.SheafOfModules.RingedSite.GradedModuleSheaf.{u, u} A) :
    isQuasicoherent A M ↔ ∀ n : ℤ, (M n).IsQuasicoherent := sorry

end SheafOfModules.RingedSite.GradedModuleSheaf

namespace AlgebraicGeometry.RelativeProjTwistPresentation

section

variable {S : Scheme.{u}}
variable (calA : GradedAlgebraSheaf.{u, u} S.sheaf)

/-- The category of degreewise quasi-coherent graded `calA`-modules. -/
abbrev Modules := (GradedModuleSheaf.isQuasicoherent calA).FullSubcategory

/-- The visible data `(d, ℒ, ψ)` of a relative-`Proj` test quadruple over `f : T ⟶ S`.

The line bundle and its invertibility instance are explicit parameters, while the structure stores
the positive degree and every homogeneous component of the graded map `ψ`. -/
structure RelativeProjTestQuadruple
    {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ S)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle] where
  /-- The positive Veronese degree. -/
  degree : ℕ
  /-- The Veronese degree is positive. -/
  positive : 1 ≤ degree
  /-- The degreewise components of `ψ : calA^(d) ⟶ f_* (⊕ n, lineBundle^⊗n)`. -/
  psi : ∀ n : ℕ, calA (Int.ofNat (n * degree)) ⟶
    (Scheme.Modules.pushforward f).obj (Scheme.Modules.tensorPowerInt lineBundle (n : ℤ))

namespace RelativeProjTestQuadruple

/-- Explicit comparison data saying that `r : T ⟶ X` is associated to a test quadruple. -/
structure AssociatedTo
    {X T : Scheme.{u}} [MonoidalCategory T.Modules] {f : T ⟶ S}
    {lineBundle : T.Modules} [Scheme.Modules.Invertible lineBundle]
    {A : S.affineOpens → Type u} {σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U} [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {sectionGradingIso : ∀ (U : S.affineOpens) (d : ℕ),
      (calA (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d}
    {sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U}
    {sectionProjDomainTop : ∀ ⦃U U' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens)), projMapDomain (sectionRestrict h) = ⊤}
    {sectionDegreeZeroIso : ∀ U : S.affineOpens,
      sectionGrading U 0 ≃+* S.presheaf.obj (Opposite.op (U : S.Opens))}
    {π : X ⟶ S}
    (presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π)
    (quadruple : RelativeProjTestQuadruple calA f lineBundle) (r : T ⟶ X) where
  /-- The associated morphism lies over `S`. -/
  over_base : r ≫ π = f
  /-- Pullback of the degree-`n d` twist is the `n`-th tensor power of the line bundle. -/
  twistIso : ∀ n : ℤ,
    (Scheme.Modules.pullback r).obj
        (presentation.twistAlgebra (n * Int.ofNat quadruple.degree)) ≅
      Scheme.Modules.tensorPowerInt lineBundle n

end RelativeProjTestQuadruple

variable (hqc : ∀ n : ℤ, (calA n).IsQuasicoherent)
variable (A : S.affineOpens → Type u) (σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionGradingIso :
  ∀ (U : S.affineOpens) (d : ℕ),
    (calA (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
variable (sectionRestrict :
  ∀ ⦃U U' : S.affineOpens⦄,
    (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens)),
    ∀ d : ℕ, ∀ x : sectionGrading U' d,
      sectionGradingIso U d
          ((((calA (Int.ofNat d)).val.map (homOfLE h).op).hom)
            ((sectionGradingIso U' d).symm x)) =
        (sectionRestrict h).gradedAddHom d x)
variable (sectionProjDomainTop :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens)),
    projMapDomain (sectionRestrict h) = ⊤)
variable (sectionDegreeZeroIso :
  ∀ U : S.affineOpens,
    sectionGrading U 0 ≃+* S.presheaf.obj (Opposite.op (U : S.Opens)))
variable {X : Scheme.{u}} (π : X ⟶ S)

/-- Explicit functorial data for the associated-module construction on a chosen relative-`Proj`
presentation. The functor, local formulas, comparison isomorphisms, and degree-zero map are stored
as data; only their laws are propositions. -/
structure AssociatedModuleFunctor
    (hqc : ∀ n : ℤ, (calA n).IsQuasicoherent)
    (sectionRestrict_spec :
      ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens)),
        ∀ d : ℕ, ∀ x : sectionGrading U' d,
          sectionGradingIso U d
              ((((calA (Int.ofNat d)).val.map (homOfLE h).op).hom)
                ((sectionGradingIso U' d).symm x)) =
            (sectionRestrict h).gradedAddHom d x)
    (presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π) where
  /-- The graded relative-tensor operation used in formula 27.17.0.1. -/
  relativeTensor : ∀ T : Scheme.{u}, GradedObject ℤ T.Modules → GradedObject ℤ T.Modules →
    GradedObject ℤ T.Modules → GradedObject ℤ T.Modules
  /-- The functor `M ↦ M̃`. -/
  functor : Modules calA ⥤ X.Modules
  /-- Formula 27.17.0.1 as a functor for every test quadruple. -/
  localFunctor : ∀ {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ S)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (quadruple : RelativeProjTestQuadruple calA f lineBundle), Modules calA ⥤ T.Modules
  /-- The local functor evaluates to the degree-zero relative tensor formula. -/
  localFunctor_obj : ∀ {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ S)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (quadruple : RelativeProjTestQuadruple calA f lineBundle) (M : Modules calA),
    (localFunctor f lineBundle quadruple).obj M =
      Scheme.Modules.relativeProjTilde f (fun n ↦ calA n) (fun n ↦ M.obj n)
        lineBundle (relativeTensor T)
  /-- Pullback along an associated morphism has the canonical local formula. -/
  localIso : ∀ {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ S)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (quadruple : RelativeProjTestQuadruple calA f lineBundle) (r : T ⟶ X),
    RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple r →
      ((functor ⋙ Scheme.Modules.pullback r) ≅ localFunctor f lineBundle quadruple)
  /-- The local formula is compatible with pullback of an associated quadruple. -/
  localPullbackIso : ∀ {T T' : Scheme.{u}}
    [MonoidalCategory T.Modules] [MonoidalCategory T'.Modules]
    (f : T ⟶ S) (g : T' ⟶ T)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (lineBundle' : T'.Modules) [Scheme.Modules.Invertible lineBundle']
    (quadruple : RelativeProjTestQuadruple calA f lineBundle)
    (quadruple' : RelativeProjTestQuadruple calA (g ≫ f) lineBundle') (r : T ⟶ X),
    RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple r →
      RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple' (g ≫ r) →
        ((localFunctor f lineBundle quadruple ⋙ Scheme.Modules.pullback g) ≅
          localFunctor (g ≫ f) lineBundle' quadruple')
  /-- The direct and iterated local comparisons agree objectwise. -/
  localIso_comp : ∀ {T T' : Scheme.{u}}
    [MonoidalCategory T.Modules] [MonoidalCategory T'.Modules]
    (f : T ⟶ S) (g : T' ⟶ T)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (lineBundle' : T'.Modules) [Scheme.Modules.Invertible lineBundle']
    (quadruple : RelativeProjTestQuadruple calA f lineBundle)
    (quadruple' : RelativeProjTestQuadruple calA (g ≫ f) lineBundle') (r : T ⟶ X)
    (h : RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple r)
    (h' : RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple' (g ≫ r))
    (M : Modules calA),
    (Scheme.Modules.pullbackComp g r).symm.app (functor.obj M) ≪≫
        (Scheme.Modules.pullback g).mapIso ((localIso f lineBundle quadruple r h).app M) ≪≫
        (localPullbackIso f g lineBundle lineBundle' quadruple quadruple' r h h').app M =
      (localIso (g ≫ f) lineBundle' quadruple' (g ≫ r) h').app M
  /-- The canonical degree-zero map `π^* M₀ ⟶ M̃`. -/
  degreeZero :
    (GradedModuleSheaf.isQuasicoherent calA).ι ⋙ GradedModuleSheaf.eval calA 0 ⋙
      Scheme.Modules.pullback π ⟶ functor
  /-- The associated-module functor is exact. -/
  exact : exactFunctor (Modules calA) X.Modules functor

/-- The associated-module functor carried by explicit construction data. -/
def associated
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) : Modules calA ⥤ X.Modules :=
  construction.functor

/-- Formula 27.17.0.1 as a functor for explicit associated-module construction data. -/
def localTildeFunctor
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation)
    {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ S)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (quadruple : RelativeProjTestQuadruple calA f lineBundle) : Modules calA ⥤ T.Modules :=
  construction.localFunctor f lineBundle quadruple

/-- The chosen local functor has exactly the degree-zero graded relative-tensor formula. -/
theorem localTildeFunctor_obj
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation)
    {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ S)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (quadruple : RelativeProjTestQuadruple calA f lineBundle) (M : Modules calA) :
    (localTildeFunctor calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
      sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction f
      lineBundle quadruple).obj M =
      Scheme.Modules.relativeProjTilde f (fun n ↦ calA n) (fun n ↦ M.obj n)
        lineBundle (construction.relativeTensor T) := sorry

/-- The canonical local comparison with formula 27.17.0.1. -/
def associatedLocalIso
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation)
    {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ S)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (quadruple : RelativeProjTestQuadruple calA f lineBundle) (r : T ⟶ X)
    (h : RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple r) :
    construction.functor ⋙ Scheme.Modules.pullback r ≅
      localTildeFunctor calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
        sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction f
        lineBundle quadruple :=
  construction.localIso f lineBundle quadruple r h

/-- The objectwise component of the canonical local comparison. -/
def associatedLocalIso_app
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation)
    {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ S)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (quadruple : RelativeProjTestQuadruple calA f lineBundle) (r : T ⟶ X)
    (h : RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple r)
    (M : Modules calA) :
    (Scheme.Modules.pullback r).obj (construction.functor.obj M) ≅
      (localTildeFunctor calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
        sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction f
        lineBundle quadruple).obj M :=
  (associatedLocalIso calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
    sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction f lineBundle
    quadruple r h).app M

/-- The local comparison is compatible with pullback. -/
theorem associatedLocalIso_comp
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation)
    {T T' : Scheme.{u}} [MonoidalCategory T.Modules] [MonoidalCategory T'.Modules]
    (f : T ⟶ S) (g : T' ⟶ T)
    (lineBundle : T.Modules) [Scheme.Modules.Invertible lineBundle]
    (lineBundle' : T'.Modules) [Scheme.Modules.Invertible lineBundle']
    (quadruple : RelativeProjTestQuadruple calA f lineBundle)
    (quadruple' : RelativeProjTestQuadruple calA (g ≫ f) lineBundle') (r : T ⟶ X)
    (h : RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple r)
    (h' : RelativeProjTestQuadruple.AssociatedTo calA presentation quadruple' (g ≫ r))
    (M : Modules calA) :
    (Scheme.Modules.pullbackComp g r).symm.app (construction.functor.obj M) ≪≫
        (Scheme.Modules.pullback g).mapIso
          (associatedLocalIso_app calA hqc A σ sectionGrading P sectionGradingIso
            sectionRestrict sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π
            construction f lineBundle quadruple r h M) ≪≫
        (construction.localPullbackIso f g lineBundle lineBundle' quadruple quadruple' r h h').app M =
      associatedLocalIso_app calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
        sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction (g ≫ f)
        lineBundle' quadruple' (g ≫ r) h' M := sorry

/-- The canonical natural map `π^* M₀ ⟶ M̃`. -/
def degreeZeroToAssociated
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) :
    (GradedModuleSheaf.isQuasicoherent calA).ι ⋙ GradedModuleSheaf.eval calA 0 ⋙
      Scheme.Modules.pullback π ⟶ construction.functor :=
  construction.degreeZero

/-- The component of the degree-zero map at `M`. -/
def degreeZeroToAssociated_app
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) (M : Modules calA) :
    (Scheme.Modules.pullback π).obj (M.obj 0) ⟶ construction.functor.obj M :=
  (degreeZeroToAssociated calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
    sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction).app M

/-- A chosen associated-module construction is exact. -/
theorem associatedExact
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) : exactFunctor (Modules calA) X.Modules construction.functor := sorry

end

end AlgebraicGeometry.RelativeProjTwistPresentation
