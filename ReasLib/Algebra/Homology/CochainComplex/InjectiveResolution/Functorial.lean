/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Resolution
public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Map
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Functorial
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Injective Resolutions of Bounded-Below Cochain Complexes

This leaf owns the strict, cochain-level form of a functorial injective resolution. Its primary
data are a functor into the category of quasi-isomorphisms to bounded-below termwise-injective
complexes and a strict section of the source projection. Passing to the homotopy category is
separate derived API, so downstream constructions can use either level without rebuilding the
resolution-arrow category.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Stacks 0141: the category of bounded-below injective-resolution arrows `K ⟶ I`, where `I`
has injective terms and the arrow is a quasi-isomorphism. -/
@[stacks 0141]
abbrev InjRes :=
  ObjectProperty.FullSubcategory
    (fun X :
      Comma
        (𝟭 (Plus A))
        (ObjectProperty.ι
          (fun I : Plus A ↦ ∀ n : ℤ, Injective (I.obj.X n))) ↦
      QuasiIso X.hom.hom)

namespace InjRes

/-- The canonical inclusion of injective-resolution arrows into the ambient comma category. -/
abbrev ι :
    InjRes A ⥤
      Comma
        (𝟭 (Plus A))
        (ObjectProperty.ι
          (fun I : Plus A ↦ ∀ n : ℤ, Injective (I.obj.X n))) :=
  ObjectProperty.ι _

/-- The source complex of an injective-resolution arrow. -/
abbrev source : InjRes A ⥤ Plus A :=
  ι A ⋙ Comma.fst _ _

/-- The termwise-injective target of an injective-resolution arrow. -/
@[stacks 0141]
abbrev target : InjRes A ⥤ InjectivePlus A :=
  ι A ⋙ Comma.snd _ _

/-- The target of an injective-resolution arrow, viewed as a bounded-below cochain complex. -/
@[stacks 0141]
abbrev targetPlus : InjRes A ⥤ Plus A :=
  target A ⋙ ObjectProperty.ι _

/-- The source of an injective-resolution arrow, viewed as an ambient cochain complex. -/
@[stacks 0141]
abbrev sourceComplex : InjRes A ⥤ CochainComplex A ℤ :=
  source A ⋙ Plus.ι A

/-- The target of an injective-resolution arrow, viewed as an ambient cochain complex. -/
@[stacks 0141]
abbrev complex : InjRes A ⥤ CochainComplex A ℤ :=
  target A ⋙ InjectivePlus.ι A

/-- The canonical comparison from the source to the target of an injective-resolution arrow. -/
@[stacks 0141]
def comparison : source A ⟶ targetPlus A :=
  Functor.whiskerLeft (ι A)
    (Comma.natTrans (𝟭 (Plus A))
      (ObjectProperty.ι (fun I : Plus A ↦ ∀ n : ℤ, Injective (I.obj.X n))))

/-- The canonical comparison, viewed as a natural transformation of ambient cochain
complexes. -/
@[stacks 0141]
def comparisonComplex : sourceComplex A ⟶ complex A :=
  Functor.whiskerRight (comparison A) (Plus.ι A)

/-- The target functor returns the target of the underlying resolution arrow. -/
@[simp, stacks 0141]
theorem target_obj (X : InjRes A) :
    (target A).obj X = ((ι A).obj X).right := sorry

/-- The canonical comparison is the arrow of the underlying comma object. -/
@[simp, stacks 0141]
theorem comparison_app (X : InjRes A) :
    (comparison A).app X = ((ι A).obj X).hom := sorry

/-- The termwise-injective target of an injective-resolution arrow, viewed in the bounded-below
homotopy category. -/
@[stacks 0141]
noncomputable abbrev targetHomotopy :
    InjRes A ⥤ HomotopyCategory.Plus.Injective A :=
  target A ⋙ InjectivePlus.toHomotopy A

end InjRes

/-- Stacks 0141: a functorial bounded-below injective resolution is a strict section of the
source functor on the category of injective-resolution arrows. -/
@[stacks 0141]
structure FunctorialInjectiveResolution where
  /-- The chosen injective-resolution arrow for every bounded-below complex. -/
  toFunctor : Plus A ⥤ InjRes A
  /-- Forgetting the target and comparison arrow recovers the source complex strictly. -/
  toFunctor_comp_source : toFunctor ⋙ InjRes.source A = 𝟭 (Plus A)

namespace FunctorialInjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The functorial termwise-injective target selected by `J`. -/
@[stacks 0141]
abbrev target (J : FunctorialInjectiveResolution A) : Plus A ⥤ InjectivePlus A :=
  J.toFunctor ⋙ InjRes.target A

/-- The functorial target selected by `J`, viewed as a bounded-below cochain complex. -/
@[stacks 0141]
abbrev targetPlus (J : FunctorialInjectiveResolution A) : Plus A ⥤ Plus A :=
  J.toFunctor ⋙ InjRes.targetPlus A

/-- The functorial target selected by `J`, viewed as an ambient cochain complex. -/
@[stacks 0141]
abbrev complex (J : FunctorialInjectiveResolution A) :
    Plus A ⥤ CochainComplex A ℤ :=
  J.target ⋙ InjectivePlus.ι A

/-- The natural quasi-isomorphism candidate from a bounded-below complex to its functorial
termwise-injective target. -/
@[stacks 0141]
def comparison (J : FunctorialInjectiveResolution A) :
    𝟭 (Plus A) ⟶ J.targetPlus :=
  eqToHom J.toFunctor_comp_source.symm ≫
    Functor.whiskerLeft J.toFunctor (InjRes.comparison A)

/-- The functorial comparison, viewed as a natural transformation of ambient cochain
complexes. -/
@[stacks 0141]
def comparisonComplex (J : FunctorialInjectiveResolution A) :
    Plus.ι A ⟶ J.complex :=
  Functor.whiskerRight J.comparison (Plus.ι A)

/-- The source of the chosen injective-resolution arrow for `K` is `K`. -/
theorem source_obj_eq (J : FunctorialInjectiveResolution A) (K : Plus A) :
    ((InjRes.ι A).obj (J.toFunctor.obj K)).left = K := sorry

/-- The comparison arrow extracted from a functorial injective resolution is a quasi-isomorphism. -/
theorem resolution_quasiIso (J : FunctorialInjectiveResolution A) (K : Plus A) :
    QuasiIso (J.comparisonComplex.app K) := sorry

/-- The strict functorial injective resolution as a functorial right resolution along the
bounded-below inclusion. -/
@[stacks 0141]
def toFunctorialAlong (J : FunctorialInjectiveResolution A) :
    LocalizerMorphism.RightResolution.FunctorialAlong
      (Plus.TermsIn.localizer (isInjective A)) (Plus.ι A) where
  model := J.target
  comparison := J.comparisonComplex
  comparison_mem := J.resolution_quasiIso

/-- The injective resolution of `K` extracted from a functorial injective resolution. -/
def resolution (J : FunctorialInjectiveResolution A) (K : Plus A) :
    InjectiveResolution K.obj :=
  J.toFunctorialAlong.resolution K

/-- The bundled resolving model is the value of the functorial injective target. -/
@[simp, stacks 0141]
theorem resolution_model (J : FunctorialInjectiveResolution A) (K : Plus A) :
    (J.resolution K).model = J.target.obj K := sorry

/-- The resolving complex underlies the value of the functorial injective target. -/
@[simp, stacks 0141]
theorem resolution_complex (J : FunctorialInjectiveResolution A) (K : Plus A) :
    (J.resolution K).complex = (J.target.obj K : CochainComplex A ℤ) := sorry

/-- The resolution morphism is the component of the functorial comparison. -/
@[simp, stacks 0141]
theorem resolution_ι (J : FunctorialInjectiveResolution A) (K : Plus A) :
    (J.resolution K).ι = J.comparisonComplex.app K := sorry

/-- A morphism of bounded-below complexes induces a map between the functorially selected
injective resolutions. -/
@[stacks 0141]
def map (J : FunctorialInjectiveResolution A) {K L : Plus A} (f : K ⟶ L) :
    InjectiveResolution.Map f.hom (J.resolution K) (J.resolution L) :=
  J.toFunctorialAlong.map f

/-- The model map of the functorial resolution map is the map selected by `J.target`. -/
@[simp, stacks 0141]
theorem map_modelHom (J : FunctorialInjectiveResolution A) {K L : Plus A} (f : K ⟶ L) :
    (J.map f).modelHom = J.target.map f := sorry

/-- The ambient cochain map of the functorial resolution map is the map selected by
`J.complex`. -/
@[simp, stacks 0141]
theorem map_hom (J : FunctorialInjectiveResolution A) {K L : Plus A} (f : K ⟶ L) :
    (J.map f).hom = J.complex.map f := sorry

/-- The functorial resolution map commutes with the comparison morphisms. -/
@[reassoc, stacks 0141]
theorem map_naturality (J : FunctorialInjectiveResolution A) {K L : Plus A} (f : K ⟶ L) :
    (J.resolution K).ι ≫ (J.map f).hom = f.hom ≫ (J.resolution L).ι := sorry

/-- The map selected over an identity is the identity resolution map after reindexing. -/
@[simp, stacks 0141]
theorem map_id (J : FunctorialInjectiveResolution A) (K : Plus A) :
    InjectiveResolution.Map.reindex ((Plus.ι A).map_id K)
        (J.map (𝟙 K)) = InjectiveResolution.Map.id (J.resolution K) := sorry

/-- The map selected over a composite is the composite of the selected resolution maps after
reindexing. -/
@[simp, stacks 0141]
theorem map_comp (J : FunctorialInjectiveResolution A) {K L M : Plus A}
    (f : K ⟶ L) (g : L ⟶ M) :
    J.map (f ≫ g) = InjectiveResolution.Map.reindex ((Plus.ι A).map_comp f g).symm
      (InjectiveResolution.Map.comp (J.map f) (J.map g)) := sorry

/-- The objectwise injective-resolution choice underlying a functorial injective resolution. -/
noncomputable def toInjectiveResolutionChoice (J : FunctorialInjectiveResolution A) :
    InjectiveResolutionChoice A :=
  fun K ↦ J.resolution K

/-- A homotopy-category realization of a strict functorial injective resolution. The natural
isomorphism records the formal, choice-invariant version of the source statement that the
homotopy resolution functor agrees with the injective-target functor. -/
structure HomotopyRealization (J : FunctorialInjectiveResolution A) where
  /-- The functorial bounded-below injective resolution in the homotopy category. -/
  resolutionFunctor : HomotopyCategory.Plus.InjectiveResolutionFunctor A
  /-- The homotopy resolution realizes the objectwise resolutions selected by `J`. -/
  realizesChoice :
    InjectiveResolutionChoice.IsRealizedBy A J.toInjectiveResolutionChoice resolutionFunctor
  /-- On bounded-below complexes, the homotopy resolution agrees with the target of the selected
  injective-resolution arrows. -/
  targetIso :
    HomotopyCategory.Plus.quotient A ⋙ resolutionFunctor.toFunctor ≅
      J.target ⋙ InjectivePlus.toHomotopy A
  /-- The target comparison intertwines the resolution comparison with the
  comparison selected by the strict functorial resolution. -/
  targetIso_fac (K : Plus A) :
    resolutionFunctor.ι.app ((HomotopyCategory.Plus.quotient A).obj K) ≫
        (HomotopyCategory.Plus.Injective.ι A).map (targetIso.hom.app K) =
      InjectiveResolutionChoice.comparison A J.toInjectiveResolutionChoice K

namespace HomotopyRealization

variable {J : FunctorialInjectiveResolution A}

/-- The inverse target comparison carries the selected comparison back to the
comparison of the homotopy resolution functor. -/
@[reassoc]
theorem targetIso_inv_fac (H : HomotopyRealization J) (K : Plus A) :
    InjectiveResolutionChoice.comparison A J.toInjectiveResolutionChoice K ≫
        (HomotopyCategory.Plus.Injective.ι A).map (H.targetIso.inv.app K) =
      H.resolutionFunctor.ι.app ((HomotopyCategory.Plus.quotient A).obj K) := sorry

/-- The component of the target comparison is the unique objectwise
comparison compatible with the resolution morphisms. -/
theorem targetIso_hom_app_unique (H : HomotopyRealization J) (K : Plus A)
    (eK : H.resolutionFunctor.toFunctor.obj
          ((HomotopyCategory.Plus.quotient A).obj K) ≅
        InjectiveResolutionChoice.homotopyObj A J.toInjectiveResolutionChoice K)
    (h_eK : H.resolutionFunctor.ι.app
          ((HomotopyCategory.Plus.quotient A).obj K) ≫
        (HomotopyCategory.Plus.Injective.ι A).map eK.hom =
          InjectiveResolutionChoice.comparison A J.toInjectiveResolutionChoice K) :
    H.targetIso.hom.app K = eK.hom := sorry

/-- The target comparison is the unique natural isomorphism compatible with
the comparison morphisms of the two resolution constructions. -/
theorem targetIso_unique (H : HomotopyRealization J)
    (e : HomotopyCategory.Plus.quotient A ⋙ H.resolutionFunctor.toFunctor ≅
      J.target ⋙ InjectivePlus.toHomotopy A)
    (h_e : ∀ K : Plus A,
      H.resolutionFunctor.ι.app ((HomotopyCategory.Plus.quotient A).obj K) ≫
          (HomotopyCategory.Plus.Injective.ι A).map (e.hom.app K) =
        InjectiveResolutionChoice.comparison A J.toInjectiveResolutionChoice K) :
    e = H.targetIso := sorry

end HomotopyRealization

/-- Stacks 05TL: a strict functorial injective resolution has a compatible realization in the
bounded-below injective homotopy category. -/
@[stacks 05TL]
theorem nonempty_homotopyRealization (J : FunctorialInjectiveResolution A) :
    Nonempty (HomotopyRealization J) := sorry

/-- Stacks 0141: functorial injective embeddings produce strict functorial bounded-below
injective resolutions. -/
@[stacks 0141]
theorem nonempty [HasFunctorialInjectives A] :
    Nonempty (FunctorialInjectiveResolution A) := sorry

end FunctorialInjectiveResolution

end CochainComplex
