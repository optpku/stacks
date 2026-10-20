/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineTypes
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit
public import ReasLib.AlgebraicGeometry.FormalSpectrum.PowerStages
public import ReasLib.RingTheory.AdicCompletion.Topology

/-!
# Affine formal completions along a closed subset

The functor-of-points completion of an affine scheme along a closed subset,
its quotient-power comparison, and the resulting formal-completion properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The closed subset `V(I) ⊆ Spec(A)`. -/
def zeroLocusCloseds {A : Type u} [CommRing A] (I : Ideal A) :
    Closeds (Spec (.of A)) where
  carrier := PrimeSpectrum.zeroLocus (I : Set A)
  isClosed' := PrimeSpectrum.isClosed_zeroLocus (I : Set A)

/-- The carrier of `zeroLocusCloseds I` is `PrimeSpectrum.zeroLocus I`. -/
theorem zeroLocusCloseds_carrier {A : Type u} [CommRing A] (I : Ideal A) :
    (zeroLocusCloseds I : Set (Spec (.of A))) =
      PrimeSpectrum.zeroLocus (I : Set A) :=
  sorry

/-- Membership in `zeroLocusCloseds I` is membership in `V(I)`. -/
theorem mem_zeroLocusCloseds {A : Type u} [CommRing A] (I : Ideal A)
    (x : Spec (.of A)) :
    x ∈ zeroLocusCloseds I ↔ x ∈ PrimeSpectrum.zeroLocus (I : Set A) :=
  sorry

/-- For a closed subset of an affine scheme, compactness of its complement is
equivalent to constructibility. -/
theorem isCompact_compl_iff_isConstructible {A : Type u} [CommRing A]
    (T : Closeds (Spec (.of A))) :
    IsCompact (T : Set (Spec (.of A)))ᶜ ↔
      Topology.IsConstructible (T : Set (Spec (.of A))) :=
  sorry

/-- A compact-open complement of a closed subset of `Spec(A)` is cut out by a
finitely generated ideal. -/
theorem exists_fgIdeal_eq_zeroLocus_of_isCompact_compl {A : Type u}
    [CommRing A] (T : Closeds (Spec (.of A)))
    (hT : IsCompact (T : Set (Spec (.of A)))ᶜ) :
    ∃ (I : Ideal A), I.FG ∧ T = zeroLocusCloseds I :=
  sorry

/-- A Yoneda section maps into a specified subset of `Spec(A)`. -/
def mapsInto {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Set (Spec (.of A)))
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj (Over.mk structureHom)).obj U) : Prop :=
  Set.range (x : unop U ⟶ Over.mk structureHom).left ⊆ T

/-- The landing condition `mapsInto structureHom T x` unfolds to range
containment in `T`. -/
theorem mapsInto_iff {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Set (Spec (.of A)))
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj (Over.mk structureHom)).obj U) :
    mapsInto structureHom T x ↔
      Set.range (x : unop U ⟶ Over.mk structureHom).left ⊆ T :=
  sorry

/-- The landing condition is stable under precomposition over `S`. -/
theorem mapsInto_map {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) {T : Set (Spec (.of A))}
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V)
    {x : (yoneda.obj (Over.mk structureHom)).obj U}
    (hx : mapsInto structureHom T x) :
    mapsInto structureHom T ((yoneda.obj (Over.mk structureHom)).map φ x) :=
  sorry

/-- A Yoneda section whose image lands in a closed subset. -/
abbrev affineCompletionAlongObj {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    (U : (Over S)ᵒᵖ) :=
  { x : (yoneda.obj (Over.mk structureHom)).obj U // mapsInto structureHom T x }

/-- Precomposition sends landing sections to landing sections. -/
def affineCompletionAlongMap {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    {U V : (Over S)ᵒᵖ} (testHom : U ⟶ V) :
    affineCompletionAlongObj structureHom T U ⟶ affineCompletionAlongObj structureHom T V :=
  TypeCat.ofHom fun sectionPoint ↦
    ⟨(yoneda.obj (Over.mk structureHom)).map testHom sectionPoint.1,
      mapsInto_map structureHom testHom sectionPoint.2⟩

/-- Precomposition by an identity fixes each landing section. -/
theorem affineCompletionAlongMap_id {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A))) (U : (Over S)ᵒᵖ) :
    affineCompletionAlongMap structureHom T (𝟙 U) =
      𝟙 (affineCompletionAlongObj structureHom T U) := sorry

/-- Precomposition of landing sections preserves composition. -/
theorem affineCompletionAlongMap_comp {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    {U V W : (Over S)ᵒᵖ} (first : U ⟶ V) (second : V ⟶ W) :
    affineCompletionAlongMap structureHom T (first ≫ second) =
      affineCompletionAlongMap structureHom T first ≫
        affineCompletionAlongMap structureHom T second := sorry

/-- The functor-of-points completion along a closed subset of `Spec(A)`. -/
def affineCompletionAlong {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A))) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj U := affineCompletionAlongObj structureHom T U
  map testHom := affineCompletionAlongMap structureHom T testHom
  map_id U := affineCompletionAlongMap_id structureHom T U
  map_comp first second := affineCompletionAlongMap_comp structureHom T first second

/-- Objects of the completion functor are the corresponding landing sections. -/
theorem affineCompletionAlong_obj {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    (U : (Over S)ᵒᵖ) :
    (affineCompletionAlong structureHom T).obj U =
      affineCompletionAlongObj structureHom T U :=
  sorry

/-- Subtype projection from landing sections is natural under precomposition. -/
theorem affineCompletionAlong.ι_naturality {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    {U V : (Over S)ᵒᵖ} (testHom : U ⟶ V) :
    (affineCompletionAlong structureHom T).map testHom ≫
        (TypeCat.ofHom fun (sectionPoint : affineCompletionAlongObj structureHom T V) ↦
          sectionPoint.1) =
      (TypeCat.ofHom fun (sectionPoint : affineCompletionAlongObj structureHom T U) ↦
        sectionPoint.1) ≫ (yoneda.obj (Over.mk structureHom)).map testHom := sorry

/-- The canonical inclusion of the completion along `T` into the Yoneda functor. -/
def affineCompletionAlong.ι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A))) :
    affineCompletionAlong structureHom T ⟶ yoneda.obj (Over.mk structureHom) where
  app U := TypeCat.ofHom fun (x : affineCompletionAlongObj structureHom T U) ↦ x.1
  naturality _ _ testHom := affineCompletionAlong.ι_naturality structureHom T testHom

/-- Components of `affineCompletionAlong.ι` are subtype projections. -/
theorem affineCompletionAlong.ι_app {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    (U : (Over S)ᵒᵖ) :
    (affineCompletionAlong.ι structureHom T).app U =
      TypeCat.ofHom fun (x : affineCompletionAlongObj structureHom T U) ↦ x.1 :=
  sorry

/-- A Yoneda section lands in `T` exactly when it lifts through the completion. -/
theorem affineCompletionAlong.exists_lift {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) {U : (Over S)ᵒᵖ}
    (x : (yoneda.obj (Over.mk structureHom)).obj U) :
    mapsInto structureHom T x ↔
      ∃ y, (affineCompletionAlong.ι structureHom T).app U y = x :=
  sorry

/-- Completion along a closed subset of an affine scheme is an fppf sheaf. -/
theorem affineCompletionAlong_isSheaf {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (affineCompletionAlong structureHom T) := sorry

/-- Every section of a quotient-power stage maps into the zero locus of the ideal. -/
theorem powerStage_mapsInto {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ)
    (U : (Over S)ᵒᵖ) (sectionPoint : (yoneda.obj (powerStage structureHom I n)).obj U) :
    mapsInto structureHom (zeroLocusCloseds I)
      ((yoneda.map (powerStageToSpec structureHom I n)).app U sectionPoint) := sorry

/-- A quotient-power section gives a section of the completion along the zero locus. -/
def powerStageιApp {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) (U : (Over S)ᵒᵖ) :
    (yoneda.obj (powerStage structureHom I n)).obj U ⟶
      affineCompletionAlongObj structureHom (zeroLocusCloseds I) U :=
  TypeCat.ofHom fun sectionPoint ↦
    ⟨(yoneda.map (powerStageToSpec structureHom I n)).app U sectionPoint,
      powerStage_mapsInto structureHom I n U sectionPoint⟩

/-- The quotient-power section maps commute with precomposition. -/
theorem powerStageιApp_naturality {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ)
    {U V : (Over S)ᵒᵖ} (testHom : U ⟶ V) :
    (yoneda.obj (powerStage structureHom I n)).map testHom ≫
        powerStageιApp structureHom I n V =
      powerStageιApp structureHom I n U ≫
        (affineCompletionAlong structureHom (zeroLocusCloseds I)).map testHom := sorry

/-- The map from a quotient power stage to the completion along its zero locus. -/
def powerStageι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    yoneda.obj (powerStage structureHom I n) ⟶
      affineCompletionAlong structureHom (zeroLocusCloseds I) where
  app U := powerStageιApp structureHom I n U
  naturality _ _ testHom := powerStageιApp_naturality structureHom I n testHom

/-- The underlying section of `powerStageι` is the Yoneda image of the stage map. -/
theorem powerStageι_app {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ)
    (U : (Over S)ᵒᵖ) (f : (yoneda.obj (powerStage structureHom I n)).obj U) :
    (affineCompletionAlong.ι structureHom (zeroLocusCloseds I)).app U
        ((powerStageι structureHom I n).app U f) =
      (yoneda.map (powerStageToSpec structureHom I n)).app U f :=
  sorry

/-- The quotient-power maps into the completion commute with stage transitions. -/
theorem powerCocone_naturality {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) {m n : ℕ} (transitionHom : m ⟶ n) :
    (powerThickenings structureHom I ⋙ yoneda).map transitionHom ≫
        powerStageι structureHom I n = powerStageι structureHom I m := sorry

/-- The cocone of quotient power stages valued in the completion along `V(I)`. -/
def powerCocone {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    Cocone (powerThickenings structureHom I ⋙ yoneda) where
  pt := affineCompletionAlong structureHom (zeroLocusCloseds I)
  ι := { app n := powerStageι structureHom I n
         naturality := fun _ _ transitionHom ↦ powerCocone_naturality structureHom I transitionHom }

/-- Components of `powerCocone` are the maps `powerStageι`. -/
theorem powerCocone_ι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (powerCocone structureHom I).ι.app n = powerStageι structureHom I n :=
  sorry

/-- The presheaf comparison from the power-stage colimit to the completion. -/
def toCompletionAlong {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletion structureHom I ⟶
      affineCompletionAlong structureHom (zeroLocusCloseds I) :=
  colimit.desc (powerThickenings structureHom I ⋙ yoneda)
    (powerCocone structureHom I)

/-- The comparison restricts to `powerStageι` on every stage. -/
theorem toCompletionAlong_ι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    spfAdicCompletionι structureHom I n ≫ toCompletionAlong structureHom I =
      powerStageι structureHom I n :=
  sorry

/-- The presheaf comparison is bijective on quasi-compact test schemes. -/
def toCompletionAlong.BijectiveOnQuasiCompact {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) : Prop :=
  ∀ (U : Over S) [CompactSpace U.left],
    Function.Bijective ((toCompletionAlong structureHom I).app (op U))

/-- The quasi-compact bijectivity predicate unfolds to componentwise bijectivity. -/
theorem toCompletionAlong.bijectiveOnQuasiCompact_iff {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    toCompletionAlong.BijectiveOnQuasiCompact structureHom I ↔
      ∀ (U : Over S) [CompactSpace U.left],
        Function.Bijective ((toCompletionAlong structureHom I).app (op U)) :=
  sorry

/-- The comparison is bijective on affine test schemes under finite generation. -/
theorem toCompletionAlong.bijective_app_of_isAffine {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : I.FG) {U : Over S} [IsAffine U.left] :
    Function.Bijective ((toCompletionAlong structureHom I).app (op U)) :=
  sorry

/-- The fppf sheafification of the quotient-power presheaf colimit. -/
def spfAdicCompletionSheaf {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
    (spfAdicCompletion structureHom I)

/-- The fppf sheafification of the completion along `V(I)`. -/
def affineCompletionAlongSheaf {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
    (affineCompletionAlong structureHom T)

/-- The sheafified comparison between the power-stage spectrum and completion. -/
def sheafifiedToCompletionAlong {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spfAdicCompletionSheaf structureHom I ⟶
      affineCompletionAlongSheaf structureHom (zeroLocusCloseds I) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
    (toCompletionAlong structureHom I)

/-- Finite generation identifies the sheafified power-stage spectrum with the
formal completion along `V(I)`. -/
theorem isIso_sheafifiedToCompletionAlong_of_fg {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsIso (sheafifiedToCompletionAlong structureHom I) :=
  sorry

/-- The canonical structure morphism of the spectrum of the completed ring. -/
def completionStructureHom {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    Spec (.of (AdicCompletion.WithLimitTopology I)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion.WithLimitTopology I))) ≫
    structureHom

/-- A weak-ideal quotient of the completed ring maps to the original affine scheme
via the completion algebra map followed by the quotient map. -/
def completedStageToSpec {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (J : WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I)) :
    stage (AdicCompletion.WithLimitTopology I) (completionStructureHom structureHom I) J ⟶
      Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk J.ideal).comp (algebraMap A (AdicCompletion.WithLimitTopology I)))))
    ((congrArg (fun affineHom ↦ affineHom ≫ structureHom)
      (Spec.map_comp (CommRingCat.ofHom (algebraMap A (AdicCompletion.WithLimitTopology I)))
        (CommRingCat.ofHom (Ideal.Quotient.mk J.ideal)))).trans
      (Category.assoc _ _ structureHom))

/-- Sections of a weak-ideal quotient of the completion land in the original zero locus. -/
theorem completedStage_mapsInto {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (J : WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I)) (U : (Over S)ᵒᵖ)
    (sectionPoint : (yoneda.obj (stage (AdicCompletion.WithLimitTopology I)
      (completionStructureHom structureHom I) J)).obj U) :
    mapsInto structureHom (zeroLocusCloseds I)
      ((yoneda.map (completedStageToSpec structureHom I J)).app U sectionPoint) := sorry

/-- A section of a completed-ring quotient yields a landing section of the completion. -/
def completedStageιApp {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (J : WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I)) (U : (Over S)ᵒᵖ) :
    (yoneda.obj (stage (AdicCompletion.WithLimitTopology I)
      (completionStructureHom structureHom I) J)).obj U ⟶
        affineCompletionAlongObj structureHom (zeroLocusCloseds I) U :=
  TypeCat.ofHom fun sectionPoint ↦
    ⟨(yoneda.map (completedStageToSpec structureHom I J)).app U sectionPoint,
      completedStage_mapsInto structureHom I J U sectionPoint⟩

/-- The completed-ring landing sections commute with precomposition. -/
theorem completedStageιApp_naturality {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (J : WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I))
    {U V : (Over S)ᵒᵖ} (testHom : U ⟶ V) :
    (yoneda.obj (stage (AdicCompletion.WithLimitTopology I)
      (completionStructureHom structureHom I) J)).map testHom ≫
        completedStageιApp structureHom I J V =
      completedStageιApp structureHom I J U ≫
        (affineCompletionAlong structureHom (zeroLocusCloseds I)).map testHom := sorry

/-- The natural landing map from a completed-ring quotient stage to the completion. -/
def completedStageι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (J : WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I)) :
    yoneda.obj (stage (AdicCompletion.WithLimitTopology I)
      (completionStructureHom structureHom I) J) ⟶
        affineCompletionAlong structureHom (zeroLocusCloseds I) where
  app U := completedStageιApp structureHom I J U
  naturality _ _ testHom := completedStageιApp_naturality structureHom I J testHom

/-- The completed-ring landing maps commute with weak-ideal quotient transitions. -/
theorem completedCocone_naturality {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    {J K : WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I)} (transitionHom : J ⟶ K) :
    (thickenings (AdicCompletion.WithLimitTopology I)
      (completionStructureHom structureHom I) ⋙ yoneda).map transitionHom ≫
        completedStageι structureHom I K = completedStageι structureHom I J := sorry

/-- The canonical cocone of completed-ring quotient spectra in the completion along `V(I)`. -/
def completedCocone {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    Cocone (thickenings (AdicCompletion.WithLimitTopology I)
      (completionStructureHom structureHom I) ⋙ yoneda) where
  pt := affineCompletionAlong structureHom (zeroLocusCloseds I)
  ι := { app J := completedStageι structureHom I J
         naturality := fun _ _ transitionHom ↦
           completedCocone_naturality structureHom I transitionHom }

/-- The canonical comparison from the formal spectrum of the completed ring to
the completion along the original ideal's zero locus. -/
def completionSpfToCompletionAlong {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spf (AdicCompletion.WithLimitTopology I) (completionStructureHom structureHom I) ⟶
      affineCompletionAlongSheaf structureHom (zeroLocusCloseds I) :=
  (spf_iso_sheafify_presheafColimit (AdicCompletion.WithLimitTopology I)
    (completionStructureHom structureHom I)).hom ≫
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (colimit.desc _ (completedCocone structureHom I))

/-- The completed-ring comparison restricts to the sheafified landing map on each stage. -/
theorem completionSpfToCompletionAlong_ι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (J : WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I)) :
    spfι (AdicCompletion.WithLimitTopology I) (completionStructureHom structureHom I) J ≫
        completionSpfToCompletionAlong structureHom I =
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (completedStageι structureHom I J) := sorry

/-- For a finitely generated ideal, the formal spectrum of the completed ring is
canonically isomorphic to completion along the ideal's zero locus. -/
theorem isIso_completionSpfToCompletionAlong_of_fg {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsIso (completionSpfToCompletionAlong structureHom I) := sorry

/-- The completion along a closed subset with compact-open complement is adic*. -/
theorem isAdicStar_completionAlong_of_isCompact_compl {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A)))
    (hT : IsCompact (T : Set (Spec (.of A)))ᶜ) :
    FormalAlgebraicSpace.IsAdicStarAffine (affineCompletionAlong structureHom T) :=
  sorry

/-- For a finitely generated ideal, the power-stage comparison is bijective on
quasi-compact test schemes. -/
theorem bijective_toCompletionAlong_app {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) :
    toCompletionAlong.BijectiveOnQuasiCompact structureHom I := sorry

/-- The completion along a closed subset of a Noetherian affine scheme is
Noetherian. -/
theorem isNoetherian_completionAlong {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsNoetherian (Spec (.of A))] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    FormalAlgebraicSpace.IsNoetherianAffine (affineCompletionAlong structureHom T) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
