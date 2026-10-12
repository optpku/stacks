/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GradedObject.Total.Basic
public import stacks_project.Chap27.Lemma_27_17_1_AssociatedSheaf

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeProjTwistPresentation

section

variable {S X : Scheme.{u}}
variable (calA : GradedAlgebraSheaf.{u, u} S.sheaf)
variable (hqc : ∀ n : ℤ, (calA n).IsQuasicoherent)
variable (A : S.affineOpens → Type u) (σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionGradingIso : ∀ (U : S.affineOpens) (d : ℕ),
  (calA (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
variable (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
  (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens)),
    ∀ d : ℕ, ∀ x : sectionGrading U' d,
      sectionGradingIso U d
          ((((calA (Int.ofNat d)).val.map (homOfLE h).op).hom)
            ((sectionGradingIso U' d).symm x)) =
        (sectionRestrict h).gradedAddHom d x)
variable (sectionProjDomainTop : ∀ ⦃U U' : S.affineOpens⦄
  (h : (U : S.Opens) ≤ (U' : S.Opens)), projMapDomain (sectionRestrict h) = ⊤)
variable (sectionDegreeZeroIso : ∀ U : S.affineOpens,
  sectionGrading U 0 ≃+* S.presheaf.obj (Opposite.op (U : S.Opens)))
variable (π : X ⟶ S)

/-- Explicit integral shifts of degreewise quasi-coherent graded `calA`-modules. -/
structure GradedShift where
  /-- The shift functor `M ↦ M(n)` for every integer `n`. -/
  functor : ℤ → (Modules calA ⥤ Modules calA)
  /-- The degree-`i` term of `M(n)` is the degree-`n + i` term of `M`. -/
  obj_degree : ∀ (n : ℤ) (M : Modules calA) (i : ℤ),
    ((functor n).obj M).obj i = M.obj (n + i)
  /-- Shifted morphisms act by the original morphism in the translated degree. -/
  map_degree : ∀ (n : ℤ) {M N : Modules calA} (f : M ⟶ N) (i : ℤ),
    HEq (((functor n).map f).hom.hom i) (f.hom.hom (n + i))

namespace GradedShift

/-- Construct integral graded shifts from explicit translated functors and their degree formulas. -/
def of (functor : ℤ → (Modules calA ⥤ Modules calA))
    (obj_degree : ∀ (n : ℤ) (M : Modules calA) (i : ℤ),
      ((functor n).obj M).obj i = M.obj (n + i))
    (map_degree : ∀ (n : ℤ) {M N : Modules calA} (f : M ⟶ N) (i : ℤ),
      HEq (((functor n).map f).hom.hom i) (f.hom.hom (n + i))) : GradedShift calA where
  functor := functor
  obj_degree := obj_degree
  map_degree := map_degree

end GradedShift

/-- The homogeneous pieces of a graded module, viewed in the scheme module category. -/
def degreeFamily : Modules calA ⥤ GradedObject ℤ S.Modules where
  obj M n := M.obj n
  map f n := f.hom.hom n
  map_id := sorry
  map_comp := sorry

/-- The total graded module is the coproduct of its homogeneous pieces in `S.Modules`. -/
def total : Modules calA ⥤ S.Modules :=
  degreeFamily calA ⋙ GradedObject.Total.functor

/-- The total functor has the canonical coproduct as its object value. -/
theorem total_obj (M : Modules calA) :
    (total calA).obj M = ∐ (fun n : ℤ ↦ (M.obj n : S.Modules)) := sorry

/-- The associated sheaves of all integral shifts, as a graded-object functor. -/
def associatedShiftFamily
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) (shift : GradedShift calA) :
    Modules calA ⥤ GradedObject ℤ X.Modules where
  obj M n := construction.functor.obj ((shift.functor n).obj M)
  map f n := construction.functor.map ((shift.functor n).map f)
  map_id := sorry
  map_comp := sorry

/-- The functor `M ↦ ⨁ n : ℤ, (M(n))̃`. -/
def associatedShifts
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) (shift : GradedShift calA) : Modules calA ⥤ X.Modules :=
  associatedShiftFamily calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
      sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction shift ⋙
    GradedObject.Total.functor

/-- Objectwise, `associatedShifts` is the canonical coproduct of the associated shifts. -/
theorem associatedShifts_obj
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) (shift : GradedShift calA) (M : Modules calA) :
    (associatedShifts calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
      sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction shift).obj M =
      colimit (Discrete.functor (fun n : ℤ ↦
        construction.functor.obj ((shift.functor n).obj M))) := sorry

/-- Explicit shifted-sum comparison data for an associated-module construction. -/
structure AssociatedShiftMap
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) where
  /-- The integral shift functors used in the target direct sum. -/
  shift : GradedShift calA
  /-- The canonical natural map `π^* M ⟶ ⨁ n : ℤ, (M(n))̃`. -/
  hom : total calA ⋙ Scheme.Modules.pullback π ⟶
    associatedShifts calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
      sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction shift

namespace AssociatedShiftMap

/-- Construct shifted-sum comparison data from explicit shifts and a natural comparison map. -/
def of
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) (shift : GradedShift calA)
    (hom : total calA ⋙ Scheme.Modules.pullback π ⟶
      associatedShifts calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
        sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction shift) :
    AssociatedShiftMap calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
      sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction where
  shift := shift
  hom := hom

end AssociatedShiftMap

/-- The canonical map `π^* M ⟶ ⨁ n : ℤ, (M(n))̃` carried by explicit comparison data. -/
def gradedToAssociatedShifts
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    {construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation}
    (comparison : AssociatedShiftMap calA hqc A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π
      construction) :
    total calA ⋙ Scheme.Modules.pullback π ⟶
      associatedShifts calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
        sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction
        comparison.shift :=
  comparison.hom

/-- The component of the shifted-sum comparison at `M`. -/
def gradedToAssociatedShifts_app
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    {construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation}
    (comparison : AssociatedShiftMap calA hqc A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π
      construction) (M : Modules calA) :
    (total calA ⋙ Scheme.Modules.pullback π).obj M ⟶
      (associatedShifts calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
        sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π construction
        comparison.shift).obj M :=
  (gradedToAssociatedShifts calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
    sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π comparison).app M

end

end AlgebraicGeometry.RelativeProjTwistPresentation
