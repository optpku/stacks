module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of naive cotangent complexes

This site-generic leaf constructs the forward comparison from the inverse image of a naive
cotangent complex to the naive cotangent complex of the pulled-back ring map.  The comparison is
built from the units of the commutative-ring and module inverse-image adjunctions.  Under
representable flatness, named inverse morphisms and literal isomorphisms expose the reusable
degreewise and complex-level comparison API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf ComplexShape
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite.InverseImage
open scoped RelativeDerivation

noncomputable section

universe u

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify K CommRingCat.{u}]
variable [HasWeakSheafify K AddCommGrpCat.{u}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{u}, F.op.HasLeftKanExtension P]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}
variable [(SheafOfModules.pushforward
  (structureMap (J := J) (K := K) F O₂)).IsRightAdjoint]

namespace InverseImage

/-- The inverse image of the source naive cotangent complex. -/
@[stacks 08TM "inverse-image source complex", stacks 08TZ]
abbrev source (f : O₁ ⟶ O₂) :
    CochainComplex
      (ringedSiteModuleCategory K ((ringPullback (J := J) (K := K) F).obj O₂)) ℤ :=
  ((modulePullback (J := J) (K := K) F O₂).mapHomologicalComplex
    (up ℤ)).obj (NaiveCotangent.obj O₁ (Under.mk f))

/-- The target naive cotangent complex associated to the pulled-back ring map. -/
@[stacks 08TM "inverse-image target complex", stacks 08TZ]
abbrev target (f : O₁ ⟶ O₂) :
    CochainComplex
      (ringedSiteModuleCategory K ((ringPullback (J := J) (K := K) F).obj O₂)) ℤ :=
  NaiveCotangent.obj ((ringPullback (J := J) (K := K) F).obj O₁)
    (inverseImageUnder (J := J) (K := K) F f)

namespace Conormal

/-- The map on kernel ideals induced by the adjoint-side presentation morphism. -/
theorem ideal_le_comap (f : O₁ ⟶ O₂) (U : Cᵒᵖ) :
    conormalIdeal (FreeAlgebra.Presentation.map O₁ (Under.mk f)) U ≤
      (conormalIdeal
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f))
        (F.op.obj U)).comap
          ((Presentation.InverseImage.adjoint (J := J) (K := K) F f).hom.app U).hom := sorry

/-- The target conormal term, pushed back to the source site. -/
abbrev pushedSource (f : O₁ ⟶ O₂) :
    ringedSiteModuleCategory J O₂ :=
  Conormal.InverseImage.pushedSource (J := J) (K := K) F
    (ringUnit (J := J) (K := K) F O₂)
    (FreeAlgebra.Presentation.map
      ((ringPullback (J := J) (K := K) F).obj O₁)
      (inverseImageUnder (J := J) (K := K) F f))

/-- The canonical specialization of the generic sectionwise conormal inverse-image comparison. -/
noncomputable abbrev app (f : O₁ ⟶ O₂) (U : Cᵒᵖ) :
    conormalObj (FreeAlgebra.Presentation.map O₁ (Under.mk f)) U ⟶
      ((restrictionAlong (FreeAlgebra.Presentation.map O₁ (Under.mk f))).obj
        (pushedSource (J := J) (K := K) F f)).val.obj U :=
  Conormal.InverseImage.comparisonApp (J := J) (K := K) F
    (Presentation.InverseImage.adjoint (J := J) (K := K) F f)
    (ringUnit (J := J) (K := K) F O₂)
    (Presentation.InverseImage.adjoint_square (J := J) (K := K) F f) U

/-- On a cotangent class, the conormal comparison is the target sheafification unit applied after
the adjoint-side presentation map. -/
theorem app_toCotangent (f : O₁ ⟶ O₂) (U : Cᵒᵖ)
    (x : conormalIdeal (FreeAlgebra.Presentation.map O₁ (Under.mk f)) U) :
    app (J := J) (K := K) F f U
        ((conormalIdeal (FreeAlgebra.Presentation.map O₁ (Under.mk f)) U).toCotangent x) =
      ((conormalSourcePresheafUnit
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f))).app (F.op.obj U))
        ((conormalIdeal
          (FreeAlgebra.Presentation.map
            ((ringPullback (J := J) (K := K) F).obj O₁)
            (inverseImageUnder (J := J) (K := K) F f))
          (F.op.obj U)).toCotangent
            ⟨(Presentation.InverseImage.adjoint (J := J) (K := K) F f).hom.app U x,
              ideal_le_comap (J := J) (K := K) F f U x.2⟩) := sorry

/-- The adjoint-side canonical specialization of the generic conormal inverse-image comparison. -/
noncomputable abbrev adjoint (f : O₁ ⟶ O₂) :
    conormalSource (FreeAlgebra.Presentation.map O₁ (Under.mk f)) ⟶
      pushedSource (J := J) (K := K) F f :=
  Conormal.InverseImage.comparisonAdjoint (J := J) (K := K) F
    (Presentation.InverseImage.adjoint (J := J) (K := K) F f)
    (ringUnit (J := J) (K := K) F O₂)
    (Presentation.InverseImage.adjoint_square (J := J) (K := K) F f)

/-- The forward inverse-image comparison on the degree `-1` conormal term. -/
@[stacks 08TM "conormal comparison component"]
noncomputable abbrev map (f : O₁ ⟶ O₂) :
    (modulePullback (J := J) (K := K) F O₂).obj
        (conormalSource (FreeAlgebra.Presentation.map O₁ (Under.mk f))) ⟶
      conormalSource
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)) :=
  Conormal.InverseImage.comparison (J := J) (K := K) F
    (Presentation.InverseImage.adjoint (J := J) (K := K) F f)
    (ringUnit (J := J) (K := K) F O₂)
    (Presentation.InverseImage.adjoint_square (J := J) (K := K) F f)

/-- Transposing the conormal comparison recovers its explicit adjoint-side map. -/
@[simp]
theorem map_adj (f : O₁ ⟶ O₂) :
    (SheafOfModules.pullbackPushforwardAdjunction
      (structureMap (J := J) (K := K) F O₂)).homEquiv _ _
        (map (J := J) (K := K) F f) =
      adjoint (J := J) (K := K) F f := sorry

/-- The adjoint-side presentation map is invertible under representable flatness.  This named
instance lets the generic conormal inverse owner apply to the canonical polynomial presentation. -/
@[stacks 08TM "presentation inverse-image adjoint isomorphism"]
instance presentationAdjointMap_isIso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    IsIso (SheafOfModules.RingedSite.InverseImage.adjointMap (J := J) (K := K) F
      (Presentation.InverseImage.adjoint (J := J) (K := K) F f)) := sorry

/-- The named inverse of the degree `-1` conormal comparison.  This specialization reuses the
generic conormal inverse owner. -/
@[stacks 08TM "conormal inverse comparison morphism", stacks 08TZ]
noncomputable abbrev mapInv [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    conormalSource
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)) ⟶
      (modulePullback (J := J) (K := K) F O₂).obj
        (conormalSource (FreeAlgebra.Presentation.map O₁ (Under.mk f))) :=
  SheafOfModules.RingedSite.Conormal.InverseImage.comparisonInv
    (J := J) (K := K) F
    (Presentation.InverseImage.adjoint (J := J) (K := K) F f)
    (ringUnit (J := J) (K := K) F O₂)
    (Presentation.InverseImage.adjoint_square (J := J) (K := K) F f)

/-- The conormal comparison followed by its named inverse is the identity. -/
@[simp, stacks 08TM "conormal comparison inverse law", stacks 08TZ]
theorem map_hom_inv_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    map (J := J) (K := K) F f ≫ mapInv (J := J) (K := K) F f = 𝟙 _ := sorry

/-- The named conormal inverse followed by the forward comparison is the identity. -/
@[simp, stacks 08TM "conormal inverse comparison law", stacks 08TZ]
theorem map_inv_hom_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    mapInv (J := J) (K := K) F f ≫ map (J := J) (K := K) F f = 𝟙 _ := sorry

/-- The conormal inverse-image comparison as explicit isomorphism data, specialized from the
generic conormal comparison isomorphism. -/
@[stacks 08TM "conormal comparison isomorphism", stacks 08TZ]
noncomputable abbrev iso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (modulePullback (J := J) (K := K) F O₂).obj
        (conormalSource (FreeAlgebra.Presentation.map O₁ (Under.mk f))) ≅
      conormalSource
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)) :=
  SheafOfModules.RingedSite.Conormal.InverseImage.comparisonIso
    (J := J) (K := K) F
    (Presentation.InverseImage.adjoint (J := J) (K := K) F f)
    (ringUnit (J := J) (K := K) F O₂)
    (Presentation.InverseImage.adjoint_square (J := J) (K := K) F f)

/-- The forward map of the conormal comparison isomorphism is the canonical comparison. -/
@[simp, stacks 08TM "conormal comparison isomorphism hom", stacks 08TZ]
theorem iso_hom [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).hom = map (J := J) (K := K) F f := sorry

/-- The inverse map of the conormal comparison isomorphism is the named comparison inverse. -/
@[simp, stacks 08TM "conormal comparison isomorphism inverse", stacks 08TZ]
theorem iso_inv [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).inv = mapInv (J := J) (K := K) F f := sorry

/-- Representable flatness makes the conormal comparison invertible.  The reusable data owner is
`iso`; this theorem is the proposition-level bridge. -/
@[stacks 08TM "conormal comparison is an isomorphism", stacks 08TZ]
theorem map_isIso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    IsIso (map (J := J) (K := K) F f) := sorry

end Conormal

namespace Differentials

/-- The target differential term, pushed back to the source site. -/
abbrev pushedTerm (f : O₁ ⟶ O₂) :
    ringedSiteModuleCategory J O₂ :=
  (SheafOfModules.pushforward
    (structureMap (J := J) (K := K) F O₂)).obj
      (conormalTensorTerm
        (FreeAlgebra.Presentation.base
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f))
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)))

/-- The section function defining the adjoint-side comparison on the differential term. -/
noncomputable def app (f : O₁ ⟶ O₂) {U : Cᵒᵖ}
    (x : (FreeAlgebra.Presentation.underlying O₁ (Under.mk f)).obj.obj U) :
    ((restrictionAlong (FreeAlgebra.Presentation.map O₁ (Under.mk f))).obj
      (pushedTerm (J := J) (K := K) F f)).val.obj U :=
  ((extendRestrictAdj
    (FreeAlgebra.Presentation.map
      ((ringPullback (J := J) (K := K) F).obj O₁)
      (inverseImageUnder (J := J) (K := K) F f))).unit.app
        (relativeDifferentials
          (FreeAlgebra.Presentation.base
            ((ringPullback (J := J) (K := K) F).obj O₁)
            (inverseImageUnder (J := J) (K := K) F f)))).val.app (F.op.obj U)
    (((relativeDifferential
      (FreeAlgebra.Presentation.base
        ((ringPullback (J := J) (K := K) F).obj O₁)
        (inverseImageUnder (J := J) (K := K) F f))).app (F.op.obj U)).d
      ((Presentation.InverseImage.adjoint (J := J) (K := K) F f).hom.app U x))

/-- The sectionwise differential comparison is additive. -/
theorem app_add (f : O₁ ⟶ O₂) {U : Cᵒᵖ}
    (x y : (FreeAlgebra.Presentation.underlying O₁ (Under.mk f)).obj.obj U) :
    app (J := J) (K := K) F f (x + y) =
      app (J := J) (K := K) F f x +
        app (J := J) (K := K) F f y := sorry

/-- The sectionwise differential comparison satisfies the Leibniz rule. -/
theorem app_mul (f : O₁ ⟶ O₂) {U : Cᵒᵖ}
    (x y : (FreeAlgebra.Presentation.underlying O₁ (Under.mk f)).obj.obj U) :
    app (J := J) (K := K) F f (x * y) =
      x • app (J := J) (K := K) F f y +
        y • app (J := J) (K := K) F f x := sorry

/-- The sectionwise differential comparison commutes with restriction in the source site. -/
theorem app_naturality (f : O₁ ⟶ O₂)
    {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : (FreeAlgebra.Presentation.underlying O₁ (Under.mk f)).obj.obj U) :
    app (J := J) (K := K) F f
        ((FreeAlgebra.Presentation.underlying O₁ (Under.mk f)).obj.map i x) =
      (((restrictionAlong (FreeAlgebra.Presentation.map O₁ (Under.mk f))).obj
        (pushedTerm (J := J) (K := K) F f)).val.map i)
        (app (J := J) (K := K) F f x) := sorry

/-- The sectionwise differential comparison vanishes on the coefficient ring. -/
theorem app_base (f : O₁ ⟶ O₂) {U : Cᵒᵖ}
    (x : O₁.obj.obj U) :
    app (J := J) (K := K) F f
        ((FreeAlgebra.Presentation.base O₁ (Under.mk f)).hom.app U x) = 0 := sorry

/-- The relative derivation underlying inverse-image comparison on the degree `0` term. -/
noncomputable def derivation (f : O₁ ⟶ O₂) :
    Der[FreeAlgebra.Presentation.base O₁ (Under.mk f) ;
      (restrictionAlong (FreeAlgebra.Presentation.map O₁ (Under.mk f))).obj
        (pushedTerm (J := J) (K := K) F f)] where
  d {_} := AddMonoidHom.mk'
    (app (J := J) (K := K) F f)
    (app_add (J := J) (K := K) F f)
  d_mul := app_mul (J := J) (K := K) F f
  d_map := app_naturality (J := J) (K := K) F f
  d_app := app_base (J := J) (K := K) F f

/-- The differential-term comparison before extending scalars to the presented ring. -/
noncomputable def overSource (f : O₁ ⟶ O₂) :
    relativeDifferentials (FreeAlgebra.Presentation.base O₁ (Under.mk f)) ⟶
      (restrictionAlong (FreeAlgebra.Presentation.map O₁ (Under.mk f))).obj
        (pushedTerm (J := J) (K := K) F f) :=
  relativeDifferentialDesc (FreeAlgebra.Presentation.base O₁ (Under.mk f))
    (derivation (J := J) (K := K) F f)

/-- The adjoint-side comparison on the degree `0` differential term. -/
noncomputable def adjoint (f : O₁ ⟶ O₂) :
    conormalTensorTerm
        (FreeAlgebra.Presentation.base O₁ (Under.mk f))
        (FreeAlgebra.Presentation.map O₁ (Under.mk f)) ⟶
      pushedTerm (J := J) (K := K) F f :=
  ((extendRestrictAdj (FreeAlgebra.Presentation.map O₁ (Under.mk f))).homEquiv _ _).symm
    (overSource (J := J) (K := K) F f)

/-- The forward inverse-image comparison on the degree `0` differential term. -/
@[stacks 08TM "differential comparison component"]
noncomputable def map (f : O₁ ⟶ O₂) :
    (modulePullback (J := J) (K := K) F O₂).obj
        (conormalTensorTerm
          (FreeAlgebra.Presentation.base O₁ (Under.mk f))
          (FreeAlgebra.Presentation.map O₁ (Under.mk f))) ⟶
      conormalTensorTerm
        (FreeAlgebra.Presentation.base
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f))
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
    (structureMap (J := J) (K := K) F O₂)).homEquiv _ _).symm
      (adjoint (J := J) (K := K) F f)

/-- Transposing the differential-term comparison recovers its explicit adjoint-side map. -/
@[simp]
theorem map_adj (f : O₁ ⟶ O₂) :
    (SheafOfModules.pullbackPushforwardAdjunction
      (structureMap (J := J) (K := K) F O₂)).homEquiv _ _
        (map (J := J) (K := K) F f) =
      adjoint (J := J) (K := K) F f := sorry

/-- Representable flatness makes the differential-term component of inverse-image comparison
invertible.  This is the only local invertibility gate needed to construct a named inverse. -/
@[stacks 08TM "differential comparison is an isomorphism", stacks 08TZ]
instance map_isIso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    IsIso (map (J := J) (K := K) F f) := sorry

/-- The named inverse of the degree `0` differential-term comparison. -/
@[stacks 08TM "differential inverse comparison morphism", stacks 08TZ]
noncomputable def mapInv [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    conormalTensorTerm
        (FreeAlgebra.Presentation.base
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f))
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)) ⟶
      (modulePullback (J := J) (K := K) F O₂).obj
        (conormalTensorTerm
          (FreeAlgebra.Presentation.base O₁ (Under.mk f))
          (FreeAlgebra.Presentation.map O₁ (Under.mk f))) :=
  @CategoryTheory.inv _ _ _ _ (map (J := J) (K := K) F f)
    (map_isIso (J := J) (K := K) F f)

/-- The differential-term comparison followed by its named inverse is the identity. -/
@[simp, stacks 08TM "differential comparison inverse law", stacks 08TZ]
theorem map_hom_inv_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    map (J := J) (K := K) F f ≫ mapInv (J := J) (K := K) F f = 𝟙 _ := sorry

/-- The named differential-term inverse followed by the forward comparison is the identity. -/
@[simp, stacks 08TM "differential inverse comparison law", stacks 08TZ]
theorem map_inv_hom_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    mapInv (J := J) (K := K) F f ≫ map (J := J) (K := K) F f = 𝟙 _ := sorry

/-- The differential-term inverse-image comparison as explicit isomorphism data. -/
@[stacks 08TM "differential comparison isomorphism", stacks 08TZ]
noncomputable def iso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (modulePullback (J := J) (K := K) F O₂).obj
        (conormalTensorTerm
          (FreeAlgebra.Presentation.base O₁ (Under.mk f))
          (FreeAlgebra.Presentation.map O₁ (Under.mk f))) ≅
      conormalTensorTerm
        (FreeAlgebra.Presentation.base
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f))
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)) where
  hom := map (J := J) (K := K) F f
  inv := mapInv (J := J) (K := K) F f
  hom_inv_id := map_hom_inv_id (J := J) (K := K) F f
  inv_hom_id := map_inv_hom_id (J := J) (K := K) F f

/-- The forward map of the differential-term comparison isomorphism is the canonical comparison. -/
@[simp, stacks 08TM "differential comparison isomorphism hom", stacks 08TZ]
theorem iso_hom [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).hom = map (J := J) (K := K) F f := sorry

/-- The inverse map of the differential-term comparison isomorphism is its named inverse. -/
@[simp, stacks 08TM "differential comparison isomorphism inverse", stacks 08TZ]
theorem iso_inv [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).inv = mapInv (J := J) (K := K) F f := sorry

end Differentials

namespace Comparison

/-- The degreewise component of the forward inverse-image comparison. -/
@[stacks 08TM "degreewise inverse-image comparison", stacks 08TZ]
noncomputable def app (f : O₁ ⟶ O₂) (n : ℤ) :
    (source (J := J) (K := K) F f).X n ⟶
      (target (J := J) (K := K) F f).X n :=
  match n with
  | Int.negSucc 0 => Conormal.map (J := J) (K := K) F f
  | Int.ofNat 0 => Differentials.map (J := J) (K := K) F f
  | _ => 0

/-- The degreewise comparison, including the canonical zero-term identifications, as an explicit
isomorphism. -/
@[stacks 08TM "degreewise comparison isomorphism", stacks 08TZ]
noncomputable def appIso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    ∀ n : ℤ, (source (J := J) (K := K) F f).X n ≅
      (target (J := J) (K := K) F f).X n
  | Int.negSucc 0 => Conormal.iso (J := J) (K := K) F f
  | Int.ofNat 0 => Differentials.iso (J := J) (K := K) F f
  | Int.negSucc (n + 1) =>
      (modulePullback (J := J) (K := K) F O₂).mapZeroObject
  | Int.ofNat (n + 1) =>
      (modulePullback (J := J) (K := K) F O₂).mapZeroObject

/-- The forward map of the degreewise comparison isomorphism is the explicit component. -/
@[simp, stacks 08TM "degreewise comparison isomorphism hom", stacks 08TZ]
theorem appIso_hom [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    (appIso (J := J) (K := K) F f n).hom = app (J := J) (K := K) F f n := sorry

/-- The named inverse of the degreewise comparison. -/
@[stacks 08TM "degreewise inverse comparison morphism", stacks 08TZ]
noncomputable def appInv [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    (target (J := J) (K := K) F f).X n ⟶
      (source (J := J) (K := K) F f).X n :=
  (appIso (J := J) (K := K) F f n).inv

/-- The inverse map of the degreewise comparison isomorphism is the named component inverse. -/
@[simp, stacks 08TM "degreewise comparison isomorphism inverse", stacks 08TZ]
theorem appIso_inv [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    (appIso (J := J) (K := K) F f n).inv = appInv (J := J) (K := K) F f n := sorry

/-- The degreewise comparison followed by its named inverse is the identity. -/
@[simp, stacks 08TM "degreewise comparison inverse law", stacks 08TZ]
theorem app_hom_inv_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    app (J := J) (K := K) F f n ≫ appInv (J := J) (K := K) F f n = 𝟙 _ := sorry

/-- The named degreewise inverse followed by the comparison is the identity. -/
@[simp, stacks 08TM "degreewise inverse comparison law", stacks 08TZ]
theorem app_inv_hom_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    appInv (J := J) (K := K) F f n ≫ app (J := J) (K := K) F f n = 𝟙 _ := sorry

/-- Every degreewise comparison is invertible under representable flatness.  `appIso`/`appInv` are
the reusable data owners; this instance remains as a compatibility gate for downstream code that
uses the categorical `inv` projection directly. -/
@[stacks 08TM "degreewise comparison is an isomorphism", stacks 08TZ]
instance app_isIso [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    IsIso (app (J := J) (K := K) F f n) := sorry

/-- The degreewise comparison maps commute with the differentials. -/
theorem app_comm (f : O₁ ⟶ O₂) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    app (J := J) (K := K) F f i ≫
        (target (J := J) (K := K) F f).d i j =
      (source (J := J) (K := K) F f).d i j ≫
        app (J := J) (K := K) F f j := sorry

/-- The explicit degreewise isomorphisms commute with the differentials. -/
theorem appIso_comm [RepresentablyFlat F] (f : O₁ ⟶ O₂) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    (appIso (J := J) (K := K) F f i).hom ≫
        (target (J := J) (K := K) F f).d i j =
      (source (J := J) (K := K) F f).d i j ≫
        (appIso (J := J) (K := K) F f j).hom := sorry

/-- The named degreewise inverses commute with the differentials in the reverse direction. -/
theorem appInv_comm [RepresentablyFlat F] (f : O₁ ⟶ O₂) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    appInv (J := J) (K := K) F f i ≫
        (source (J := J) (K := K) F f).d i j =
      (target (J := J) (K := K) F f).d i j ≫
        appInv (J := J) (K := K) F f j := sorry

/-- Lemma 17.31.3 (08TM), Lemma 18.35.3 (08TZ): the explicit forward comparison from the inverse
image of a naive cotangent complex to the naive cotangent complex of the pulled-back ring map. -/
@[stacks 08TM "comparison morphism", stacks 08TZ]
noncomputable def map (f : O₁ ⟶ O₂) :
    source (J := J) (K := K) F f ⟶ target (J := J) (K := K) F f where
  f n := app (J := J) (K := K) F f n
  comm' i j hij := app_comm (J := J) (K := K) F f i j hij

/-- The degree-`n` component of the inverse-image comparison is `app`. -/
theorem map_f (f : O₁ ⟶ O₂) (n : ℤ) :
    (map (J := J) (K := K) F f).f n =
      app (J := J) (K := K) F f n := sorry

/-- The degree `-1` component is the explicit conormal comparison. -/
theorem map_f_negOne (f : O₁ ⟶ O₂) :
    (map (J := J) (K := K) F f).f (-1) =
      Conormal.map (J := J) (K := K) F f := sorry

/-- The degree `0` component is the explicit differential-term comparison. -/
theorem map_f_zero (f : O₁ ⟶ O₂) :
    (map (J := J) (K := K) F f).f 0 =
      Differentials.map (J := J) (K := K) F f := sorry

/-- The named inverse comparison of naive cotangent complexes, assembled from the degreewise
inverse owners. -/
@[stacks 08TM "inverse comparison morphism", stacks 08TZ]
noncomputable def mapInv [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    target (J := J) (K := K) F f ⟶ source (J := J) (K := K) F f where
  f n := appInv (J := J) (K := K) F f n
  comm' i j hij := appInv_comm (J := J) (K := K) F f i j hij

/-- The degree-`n` component of the named inverse comparison is `appInv`. -/
@[simp, stacks 08TM "degreewise inverse comparison", stacks 08TZ]
theorem mapInv_f [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    (mapInv (J := J) (K := K) F f).f n = appInv (J := J) (K := K) F f n := sorry

/-- In degree `-1`, the named inverse comparison is the conormal inverse. -/
@[stacks 08TM "degree -1 inverse comparison", stacks 08TZ]
theorem mapInv_f_negOne [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (mapInv (J := J) (K := K) F f).f (-1) =
      Conormal.mapInv (J := J) (K := K) F f := sorry

/-- In degree `0`, the named inverse comparison is the differential-term inverse. -/
@[stacks 08TM "degree 0 inverse comparison", stacks 08TZ]
theorem mapInv_f_zero [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (mapInv (J := J) (K := K) F f).f 0 =
      Differentials.mapInv (J := J) (K := K) F f := sorry

/-- The forward comparison followed by its named inverse is the identity. -/
@[simp, stacks 08TM "comparison inverse law", stacks 08TZ]
theorem map_hom_inv_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    map (J := J) (K := K) F f ≫ mapInv (J := J) (K := K) F f = 𝟙 _ := sorry

/-- The named inverse followed by the forward comparison is the identity. -/
@[simp, stacks 08TM "inverse comparison law", stacks 08TZ]
theorem map_inv_hom_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    mapInv (J := J) (K := K) F f ≫ map (J := J) (K := K) F f = 𝟙 _ := sorry

/-- Lemma 17.31.3 (08TM), Lemma 18.35.3 (08TZ): the canonical explicit isomorphism from
inverse image of the naive cotangent complex to the naive cotangent complex of the pulled-back
ring map. -/
@[stacks 08TM "comparison isomorphism", stacks 08TZ]
noncomputable def iso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    source (J := J) (K := K) F f ≅ target (J := J) (K := K) F f where
  hom := map (J := J) (K := K) F f
  inv := mapInv (J := J) (K := K) F f
  hom_inv_id := map_hom_inv_id (J := J) (K := K) F f
  inv_hom_id := map_inv_hom_id (J := J) (K := K) F f

/-- Lemma 17.31.3 (08TM), Lemma 18.35.3 (08TZ): for a representably flat morphism of sites, the
canonical comparison of naive cotangent complexes is invertible.  The reusable data owner is
`iso`; this theorem is the proposition-level bridge. -/
@[stacks 08TM "comparison is an isomorphism", stacks 08TZ]
theorem map_isIso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    IsIso (map (J := J) (K := K) F f) := sorry

/-- The forward map of the inverse-image comparison isomorphism is the explicit comparison. -/
@[simp, stacks 08TM "comparison isomorphism hom", stacks 08TZ]
theorem iso_hom [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).hom = map (J := J) (K := K) F f := sorry

/-- In degree `n`, the forward map of the inverse-image comparison isomorphism is `app`. -/
@[simp, stacks 08TM "degreewise comparison isomorphism hom", stacks 08TZ]
theorem iso_hom_f [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    (iso (J := J) (K := K) F f).hom.f n =
      app (J := J) (K := K) F f n := sorry

/-- The inverse map of the inverse-image comparison isomorphism is the named inverse comparison. -/
@[stacks 08TM "inverse comparison morphism", stacks 08TZ, simp]
theorem iso_inv [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).inv = mapInv (J := J) (K := K) F f := sorry

/-- In degree `n`, the inverse map of the comparison isomorphism is the named component inverse. -/
@[stacks 08TM "degreewise inverse comparison", stacks 08TZ, simp]
theorem iso_inv_f [RepresentablyFlat F] (f : O₁ ⟶ O₂) (n : ℤ) :
    (iso (J := J) (K := K) F f).inv.f n =
      appInv (J := J) (K := K) F f n := sorry

/-- In degree `-1`, the forward inverse-image comparison is the conormal comparison. -/
@[stacks 08TM "degree -1 comparison", stacks 08TZ]
theorem iso_hom_f_negOne [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).hom.f (-1) =
      Conormal.map (J := J) (K := K) F f := sorry

/-- In degree `0`, the forward inverse-image comparison is the differential-term comparison. -/
@[stacks 08TM "degree 0 comparison", stacks 08TZ]
theorem iso_hom_f_zero [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).hom.f 0 =
      Differentials.map (J := J) (K := K) F f := sorry

/-- In degree `-1`, the inverse comparison is the named conormal inverse. -/
@[stacks 08TM "degree -1 inverse comparison", stacks 08TZ]
theorem iso_inv_f_negOne [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).inv.f (-1) =
      Conormal.mapInv (J := J) (K := K) F f := sorry

/-- In degree `0`, the inverse comparison is the named differential-term inverse. -/
@[stacks 08TM "degree 0 inverse comparison", stacks 08TZ]
theorem iso_inv_f_zero [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (iso (J := J) (K := K) F f).inv.f 0 =
      Differentials.mapInv (J := J) (K := K) F f := sorry

end Comparison

namespace UnderlyingRing

variable [∀ P : Cᵒᵖ ⥤ RingCat.{u}, F.op.HasLeftKanExtension P]

/-- The naive cotangent complex pulled back directly through the unit on the underlying ring
sheaf. -/
abbrev source
    (f : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O₂)).IsRightAdjoint] :
    CochainComplex
      (SheafOfModules (underlyingRingPullback (J := J) (K := K) F O₂)) ℤ :=
  ((underlyingModulePullback (J := J) (K := K) F O₂).mapHomologicalComplex
    (up ℤ)).obj (NaiveCotangent.obj O₁ (Under.mk f))

/-- The pulled-back naive cotangent complex transported across an explicit identification of
the underlying coefficient ring sheaves. -/
abbrev targetOfIso
    (f : O₁ ⟶ O₂)
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O₂) ≅
      underlyingRingPullback (J := J) (K := K) F O₂) :
    CochainComplex
      (SheafOfModules (underlyingRingPullback (J := J) (K := K) F O₂)) ℤ :=
  ((SheafOfModules.restrictScalars e.inv).mapHomologicalComplex (up ℤ)).obj
    (NaiveCotangent.obj ((ringPullback (J := J) (K := K) F).obj O₁)
      (inverseImageUnder (J := J) (K := K) F f))

/-- The forward naive-cotangent comparison induced by an identification of the pulled-back
underlying coefficient ring sheaves compatible with their structure maps. -/
noncomputable def mapOfIso
    (f : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O₂)).IsRightAdjoint]
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O₂) ≅
      underlyingRingPullback (J := J) (K := K) F O₂)
    (he : structureMap (J := J) (K := K) F O₂ ≫
      (F.sheafPushforwardContinuous RingCat.{u} J K).map e.hom =
        underlyingRingUnit (J := J) (K := K) F O₂) :
    source (J := J) (K := K) F f ⟶ targetOfIso (J := J) (K := K) F f e :=
  (SheafOfModules.RingedSite.InverseImage.UnderlyingRing.Complex.objIsoOfIso
      F O₂ (up ℤ) e he (NaiveCotangent.obj O₁ (Under.mk f))).hom ≫
    ((SheafOfModules.restrictScalars e.inv).mapHomologicalComplex (up ℤ)).map
      (Comparison.map (J := J) (K := K) F f)

/-- Representable flatness makes the underlying-ring comparison induced by `e` an
isomorphism. -/
instance mapOfIso_isIso
    (f : O₁ ⟶ O₂)
    [RepresentablyFlat F]
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O₂)).IsRightAdjoint]
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O₂) ≅
      underlyingRingPullback (J := J) (K := K) F O₂)
    (he : structureMap (J := J) (K := K) F O₂ ≫
      (F.sheafPushforwardContinuous RingCat.{u} J K).map e.hom =
        underlyingRingUnit (J := J) (K := K) F O₂) :
    IsIso (mapOfIso (J := J) (K := K) F f e he) := sorry

/-- In each degree, the forward underlying-ring comparison first changes the pullback
presentation and then applies the naive cotangent comparison. -/
@[simp]
theorem mapOfIso_f
    (f : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O₂)).IsRightAdjoint]
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O₂) ≅
      underlyingRingPullback (J := J) (K := K) F O₂)
    (he : structureMap (J := J) (K := K) F O₂ ≫
      (F.sheafPushforwardContinuous RingCat.{u} J K).map e.hom =
        underlyingRingUnit (J := J) (K := K) F O₂)
    (i : ℤ) :
    (mapOfIso (J := J) (K := K) F f e he).f i =
      (SheafOfModules.RingedSite.InverseImage.UnderlyingRing.pullbackIsoOfIso
          F O₂ e he).hom.app
          ((NaiveCotangent.obj O₁ (Under.mk f)).X i) ≫
        (SheafOfModules.restrictScalars e.inv).map
          (Comparison.app (J := J) (K := K) F f i) := sorry

variable [(forget₂ CommRingCat RingCat.{u}).PreservesLeftKanExtensions F.op]
variable [K.PreservesSheafification (forget₂ CommRingCat RingCat.{u})]

/-- The canonical target after transporting along `ringSheafPullbackIso`. -/
abbrev target (f : O₁ ⟶ O₂) :
    CochainComplex
      (SheafOfModules (underlyingRingPullback (J := J) (K := K) F O₂)) ℤ :=
  targetOfIso (J := J) (K := K) F f
    (ringSheafPullbackIso (J := J) (K := K) F O₂)

/-- The forward comparison from the raw underlying-ring inverse image after transport along
`ringSheafPullbackIso`. -/
@[stacks 08TM "underlying-ring naive cotangent comparison", stacks 08TZ]
noncomputable def map
    (f : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O₂)).IsRightAdjoint] :
    source (J := J) (K := K) F f ⟶ target (J := J) (K := K) F f :=
  mapOfIso (J := J) (K := K) F f
    (ringSheafPullbackIso (J := J) (K := K) F O₂)
    (structureMap_comp_ringSheafPullbackIso_hom (J := J) (K := K) F O₂)

/-- Representable flatness makes the canonical underlying-ring comparison an isomorphism. -/
@[stacks 08TM "underlying-ring comparison is an isomorphism", stacks 08TZ]
instance map_isIso
    (f : O₁ ⟶ O₂)
    [RepresentablyFlat F]
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O₂)).IsRightAdjoint] :
    IsIso (map (J := J) (K := K) F f) := sorry

/-- The degreewise formula for the canonical forward underlying-ring comparison. -/
@[simp]
theorem map_f
    (f : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O₂)).IsRightAdjoint]
    (i : ℤ) :
    (map (J := J) (K := K) F f).f i =
      (SheafOfModules.RingedSite.InverseImage.UnderlyingRing.pullbackIso
          (J := J) (K := K) F O₂).hom.app
          ((NaiveCotangent.obj O₁ (Under.mk f)).X i) ≫
        (SheafOfModules.restrictScalars
          (ringSheafPullbackIso (J := J) (K := K) F O₂).inv).map
            (Comparison.app (J := J) (K := K) F f i) := sorry

end UnderlyingRing

end InverseImage

-- The forward comparison is assembled from adjunction units, universal derivations, cotangent
-- maps, and adjunction transposes. The concrete maps do not use the unfinished invertibility
-- proofs; any `sorryAx` below is confined to compatibility and invertibility proof debt.

end SheafOfModules.RingedSite.NaiveCotangent
