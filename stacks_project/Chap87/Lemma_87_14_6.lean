module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap87.Lemma_87_14_6_PowerStages

/-!
# Affine formal completions along a closed subset

For an affine scheme `X = Spec(A)` over `S` and a closed subset `T ⊆ X`, the
formal completion along `T` is the functor-of-points subfunctor of
`yoneda.obj (Over.mk structureHom)` classifying morphisms whose image lands in
`T`. Working with closed subsets of `Spec(A)` matches the source and keeps the
comparison to `spfAdicCompletion` on the Yoneda-colimit layer.

The completion is adic* when `X \ T` is quasi-compact, equals `Spf` of the
`I`-adic completion when `T = V(I)` for finitely generated `I` (as an
identification on quasi-compact schemes over `S`), and is Noetherian when `X`
is Noetherian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite TopologicalSpace TypeCat

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

/-- A point of `Spec(A)` lies in `zeroLocusCloseds I` if and only if it lies in
`V(I)`. -/
theorem mem_zeroLocusCloseds {A : Type u} [CommRing A] (I : Ideal A)
    (x : Spec (.of A)) :
    x ∈ zeroLocusCloseds I ↔ x ∈ PrimeSpectrum.zeroLocus (I : Set A) :=
  sorry

/-- For a closed subset of an affine scheme, the complement is quasi-compact if
and only if the subset is constructible. -/
theorem isCompact_compl_iff_isConstructible {A : Type u} [CommRing A]
    (T : Closeds (Spec (.of A))) :
    IsCompact (T : Set (Spec (.of A)))ᶜ ↔
      Topology.IsConstructible (T : Set (Spec (.of A))) :=
  sorry

/-- A compact open complement of a closed subset of `Spec(A)` is cut out by a
finitely generated ideal. -/
theorem exists_fgIdeal_eq_zeroLocus_of_isCompact_compl {A : Type u}
    [CommRing A] (T : Closeds (Spec (.of A)))
    (hT : IsCompact (T : Set (Spec (.of A)))ᶜ) :
    ∃ (I : Ideal A), I.FG ∧ T = zeroLocusCloseds I :=
  sorry

/-- A Yoneda section of `Spec(A)` over `S` maps into `T` when the underlying
scheme morphism has image contained in `T`. -/
def mapsInto {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Set (Spec (.of A)))
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj (Over.mk structureHom)).obj U) : Prop :=
  Set.range (x : unop U ⟶ Over.mk structureHom).left ⊆ T

/-- `mapsInto` is the condition that the classified morphism `U ⟶ Spec(A)`
lands in `T`. -/
theorem mapsInto_iff {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Set (Spec (.of A)))
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj (Over.mk structureHom)).obj U) :
    mapsInto structureHom T x ↔
      Set.range (x : unop U ⟶ Over.mk structureHom).left ⊆ T :=
  sorry

/-- `mapsInto` is stable under precomposition with a morphism of schemes over
`S`. -/
theorem mapsInto_map {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) {T : Set (Spec (.of A))}
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V)
    {x : (yoneda.obj (Over.mk structureHom)).obj U}
    (hx : mapsInto structureHom T x) :
    mapsInto structureHom T ((yoneda.obj (Over.mk structureHom)).map φ x) :=
  sorry

/-- A Yoneda section of `Spec(A)` over `S` whose image lands in `T`. -/
abbrev affineCompletionAlongObj {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    (U : (Over S)ᵒᵖ) :=
  { x : (yoneda.obj (Over.mk structureHom)).obj U // mapsInto structureHom T x }

/-- The functor-of-points completion of `X = Spec(A)` along a closed subset
`T ⊆ X`, as the subfunctor of `yoneda.obj (Over.mk structureHom)` classifying
morphisms whose image of points lands in `T`. -/
def affineCompletionAlong {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A))) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj U := affineCompletionAlongObj structureHom T U
  map φ := ofHom fun x ↦
    ⟨(yoneda.obj (Over.mk structureHom)).map φ x.1,
      mapsInto_map structureHom φ x.2⟩
  map_id := sorry
  map_comp := sorry

/-- Objects of `affineCompletionAlong structureHom T` are Yoneda sections of
`Spec(A)` mapping into `T`. -/
theorem affineCompletionAlong_obj {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    (U : (Over S)ᵒᵖ) :
    (affineCompletionAlong structureHom T).obj U =
      affineCompletionAlongObj structureHom T U :=
  sorry

/-- The canonical morphism from the affine completion along `T` to the Yoneda
functor of `Spec(A)` over `S`. -/
def affineCompletionAlong.ι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A))) :
    affineCompletionAlong structureHom T ⟶ yoneda.obj (Over.mk structureHom) where
  app U := ofHom fun (x : affineCompletionAlongObj structureHom T U) ↦ x.1
  naturality := sorry

/-- Components of `affineCompletionAlong.ι` are the subtype projections. -/
theorem affineCompletionAlong.ι_app {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    (U : (Over S)ᵒᵖ) :
    (affineCompletionAlong.ι structureHom T).app U =
      ofHom fun (x : affineCompletionAlongObj structureHom T U) ↦ x.1 :=
  sorry

/-- A Yoneda section of `Spec(A)` maps into `T` if and only if it lifts through
`affineCompletionAlong.ι`. -/
theorem affineCompletionAlong.exists_lift {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) {U : (Over S)ᵒᵖ}
    (x : (yoneda.obj (Over.mk structureHom)).obj U) :
    mapsInto structureHom T x ↔
      ∃ y, (affineCompletionAlong.ι structureHom T).app U y = x :=
  sorry

/-- The Yoneda morphism from the `n`-th power stage into the completion of
`Spec(A)` along `V(I)`. -/
def powerStageι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    yoneda.obj (powerStage structureHom I n) ⟶
      affineCompletionAlong structureHom (zeroLocusCloseds I) where
  app U :=
    ofHom fun f ↦
      (⟨(yoneda.map (powerStageToSpec structureHom I n)).app U f, sorry⟩ :
        affineCompletionAlongObj structureHom (zeroLocusCloseds I) U)
  naturality := sorry

/-- The underlying `Spec(A)`-section of `powerStageι` is the Yoneda image of
`powerStageToSpec`. -/
theorem powerStageι_app {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ)
    (U : (Over S)ᵒᵖ) (f : (yoneda.obj (powerStage structureHom I n)).obj U) :
    (affineCompletionAlong.ι structureHom (zeroLocusCloseds I)).app U
        ((powerStageι structureHom I n).app U f) =
      (yoneda.map (powerStageToSpec structureHom I n)).app U f :=
  sorry

/-- The cocone of power stages valued in the completion along `V(I)`. -/
def powerCocone {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    Cocone (powerThickenings structureHom I ⋙ yoneda) where
  pt := affineCompletionAlong structureHom (zeroLocusCloseds I)
  ι :=
    { app n := powerStageι structureHom I n
      naturality := sorry }

/-- Components of `powerCocone` are the morphisms `powerStageι`. -/
theorem powerCocone_ι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (powerCocone structureHom I).ι.app n = powerStageι structureHom I n :=
  sorry

/-- The canonical comparison from `Spf` of the `I`-adic completion to the
formal completion of `Spec(A)` along `V(I)`. -/
def toCompletionAlong {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletion structureHom I ⟶
      affineCompletionAlong structureHom (zeroLocusCloseds I) :=
  colimit.desc (powerThickenings structureHom I ⋙ yoneda)
    (powerCocone structureHom I)

/-- The comparison `toCompletionAlong` restricts to `powerStageι` on each
power stage. -/
theorem toCompletionAlong_ι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    spfAdicCompletionι structureHom I n ≫ toCompletionAlong structureHom I =
      powerStageι structureHom I n :=
  sorry

/-- The comparison `toCompletionAlong structureHom I` is bijective on sections
over every quasi-compact scheme over `S`. -/
def toCompletionAlong.BijectiveOnQuasiCompact {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) : Prop :=
  ∀ (U : Over S) [CompactSpace U.left],
    Function.Bijective ((toCompletionAlong structureHom I).app (op U))

/-- `toCompletionAlong.BijectiveOnQuasiCompact` is bijectivity of components at
quasi-compact schemes over `S`. -/
theorem toCompletionAlong.bijectiveOnQuasiCompact_iff {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    toCompletionAlong.BijectiveOnQuasiCompact structureHom I ↔
      ∀ (U : Over S) [CompactSpace U.left],
        Function.Bijective ((toCompletionAlong structureHom I).app (op U)) :=
  sorry

/-- The comparison is bijective on sections over every affine scheme over `S`. -/
theorem toCompletionAlong.bijective_app_of_isAffine {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : I.FG) {U : Over S} [IsAffine U.left] :
    Function.Bijective ((toCompletionAlong structureHom I).app (op U)) :=
  sorry

/-- Lemma 87.14.6 (1): If `X \ T` is quasi-compact, i.e., `T` is constructible,
then the formal completion of `X = Spec(A)` along `T` is adic*. -/
@[stacks 0GBA]
theorem isAdicStar_completionAlong_of_isCompact_compl {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A)))
    (hT : IsCompact (T : Set (Spec (.of A)))ᶜ) :
    ∃ (I : Ideal A) (hI : I.FG),
      T = zeroLocusCloseds I ∧
        toCompletionAlong.BijectiveOnQuasiCompact structureHom I :=
  sorry

/-- Lemma 87.14.6 (2): If `T = V(I)` for a finitely generated ideal `I ⊆ A`,
then the formal completion of `X = Spec(A)` along `T` is `Spf` of the
`I`-adic completion. -/
@[stacks 0GBA]
theorem bijective_toCompletionAlong_app {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) :
    toCompletionAlong.BijectiveOnQuasiCompact structureHom I :=
  sorry

/-- Lemma 87.14.6 (3): If `X = Spec(A)` is Noetherian, then the formal
completion of `X` along `T` is Noetherian. -/
@[stacks 0GBA]
theorem isNoetherian_completionAlong {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsNoetherian (Spec (.of A))] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    ∃ (I : Ideal A) (hI : I.FG),
      T = zeroLocusCloseds I ∧
        toCompletionAlong.BijectiveOnQuasiCompact structureHom I ∧
          IsNoetherianRing (AdicCompletion I A) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
