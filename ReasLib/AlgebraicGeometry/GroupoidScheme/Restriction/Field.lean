module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Presentation

/-!
# Restriction of groupoid schemes along field extensions

This module records the standard field-extension restriction of a groupoid scheme whose object
scheme is a field spectrum, together with the morphism properties of its defining diagram.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The morphism `Spec k' ⟶ G.U.left` induced by a field homomorphism `ι : k →+* k'`
and an identification `Spec k ≅ G.U.left`. -/
abbrev fieldRestrictionMap {S : Scheme.{u}} (G : GroupoidScheme S) {k k' : Type u}
    [Field k] [Field k'] (eU : Spec (CommRingCat.of k) ≅ G.U.left) (ι : k →+* k') :
    Spec (CommRingCat.of k') ⟶ G.U.left :=
  Spec.map (CommRingCat.ofHom ι) ≫ eU.hom

/-- The object over `S` obtained from a groupoid object by extension of its field of objects. -/
abbrev fieldRestrictionOver {S : Scheme.{u}} (G : GroupoidScheme S) {k k' : Type u}
    [Field k] [Field k'] (eU : Spec (CommRingCat.of k) ≅ G.U.left) (ι : k →+* k') :
    Over S :=
  Over.mk (fieldRestrictionMap G eU ι ≫ G.U.hom)

/-- The canonical morphism over `S` from the field-extension object to the original groupoid
object. -/
abbrev fieldRestriction {S : Scheme.{u}} (G : GroupoidScheme S) {k k' : Type u}
    [Field k] [Field k'] (eU : Spec (CommRingCat.of k) ≅ G.U.left) (ι : k →+* k') :
    fieldRestrictionOver G eU ι ⟶ G.U :=
  Over.homMk (fieldRestrictionMap G eU ι)

private lemma fieldExtensionFaithfullyFlat {k k' : Type u} [Field k] [Field k']
    (ι : k →+* k') : ι.FaithfullyFlat := by
  -- Local instance justification (noncanonical choice): this proof temporarily presents the explicit field homomorphism ι as its induced algebra structure.
  letI : Algebra k k' := ι.toAlgebra
  rw [← ι.algebraMap_toAlgebra, RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

private lemma surjectiveOfSectionToSpecField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X)
    (he : e ≫ f = 𝟙 _) : Surjective f := by
  let _ := he
  -- Local instance justification (proof-local temporary data): the section supplies this point solely for the proof of surjectivity onto the field spectrum.
  letI : Nonempty X := ⟨e default⟩
  simpa using (inferInstance : Surjective f)

private lemma flatToSpecField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) : Flat f := by
  infer_instance

private lemma universallyOpenToFieldIso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (e : Spec (CommRingCat.of k) ≅ Y) : UniversallyOpen f := by
  let Xover : Over (Spec (CommRingCat.of k)) := Over.mk (f ≫ e.inv)
  have hToSpec : UniversallyOpen Xover.hom := by
    simpa [Xover] using inferInstanceAs (UniversallyOpen Xover.hom)
  simpa using
    (MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyOpen) (f ≫ e.inv) e.hom).2
      hToSpec

section FieldBase

variable {S : Scheme.{u}} (G : GroupoidScheme S)
variable {k : Type u} [Field k]

/-- The source map of a groupoid scheme whose object scheme is a field spectrum is surjective. -/
theorem source_surjective_of_field
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) : Surjective G.s.left := by
  have hId : G.e.left ≫ G.s.left = 𝟙 G.U.left := congrArg Over.Hom.left G.identity_source
  have hSection :
      (eU.hom ≫ G.e.left) ≫ (G.s.left ≫ eU.inv) = 𝟙 (Spec (CommRingCat.of k)) := by
    calc
      (eU.hom ≫ G.e.left) ≫ (G.s.left ≫ eU.inv)
          = eU.hom ≫ G.e.left ≫ G.s.left ≫ eU.inv := by simp [Category.assoc]
      _ = eU.hom ≫ 𝟙 G.U.left ≫ eU.inv := by
        simpa [Category.assoc] using congrArg (fun f ↦ eU.hom ≫ f ≫ eU.inv) hId
      _ = 𝟙 _ := by simp
  have hToSpec : Surjective (G.s.left ≫ eU.inv) :=
    surjectiveOfSectionToSpecField (G.s.left ≫ eU.inv) (eU.hom ≫ G.e.left) hSection
  simpa using
    (MorphismProperty.cancel_right_of_respectsIso (P := @Surjective) (G.s.left ≫ eU.inv)
      eU.hom).2 hToSpec

/-- The source map of a groupoid scheme whose object scheme is a field spectrum is flat. -/
theorem source_flat_of_field
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) : Flat G.s.left := by
  have hToSpec : Flat (G.s.left ≫ eU.inv) := flatToSpecField (G.s.left ≫ eU.inv)
  simpa using
    (MorphismProperty.cancel_right_of_respectsIso (P := @Flat) (G.s.left ≫ eU.inv) eU.hom).2
      hToSpec

/-- The source map of a groupoid scheme whose object scheme is a field spectrum is universally
open. -/
theorem source_universallyOpen_of_field
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) : UniversallyOpen G.s.left := by
  exact universallyOpenToFieldIso G.s.left eU

/-- The target map of a groupoid scheme whose object scheme is a field spectrum is surjective. -/
theorem target_surjective_of_field
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) : Surjective G.t.left := by
  have hId : G.e.left ≫ G.t.left = 𝟙 G.U.left := congrArg Over.Hom.left G.identity_target
  have hSection :
      (eU.hom ≫ G.e.left) ≫ (G.t.left ≫ eU.inv) = 𝟙 (Spec (CommRingCat.of k)) := by
    calc
      (eU.hom ≫ G.e.left) ≫ (G.t.left ≫ eU.inv)
          = eU.hom ≫ G.e.left ≫ G.t.left ≫ eU.inv := by simp [Category.assoc]
      _ = eU.hom ≫ 𝟙 G.U.left ≫ eU.inv := by
        simpa [Category.assoc] using congrArg (fun f ↦ eU.hom ≫ f ≫ eU.inv) hId
      _ = 𝟙 _ := by simp
  have hToSpec : Surjective (G.t.left ≫ eU.inv) :=
    surjectiveOfSectionToSpecField (G.t.left ≫ eU.inv) (eU.hom ≫ G.e.left) hSection
  simpa using
    (MorphismProperty.cancel_right_of_respectsIso (P := @Surjective) (G.t.left ≫ eU.inv)
      eU.hom).2 hToSpec

/-- The target map of a groupoid scheme whose object scheme is a field spectrum is flat. -/
theorem target_flat_of_field
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) : Flat G.t.left := by
  have hToSpec : Flat (G.t.left ≫ eU.inv) := flatToSpecField (G.t.left ≫ eU.inv)
  simpa using
    (MorphismProperty.cancel_right_of_respectsIso (P := @Flat) (G.t.left ≫ eU.inv) eU.hom).2
      hToSpec

/-- The target map of a groupoid scheme whose object scheme is a field spectrum is universally
open. -/
theorem target_universallyOpen_of_field
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) : UniversallyOpen G.t.left := by
  exact universallyOpenToFieldIso G.t.left eU

end FieldBase

section FieldRestriction

variable {S : Scheme.{u}} (G : GroupoidScheme S)
variable {k k' : Type u} [Field k] [Field k']
variable (eU : Spec (CommRingCat.of k) ≅ G.U.left) (ι : k →+* k')

/-- The field-extension morphism on groupoid objects is surjective. -/
theorem fieldRestriction_surjective :
    Surjective (fieldRestriction G eU ι).left := by
  change Surjective (fieldRestrictionMap G eU ι)
  have hSpec : Surjective (Spec.map (CommRingCat.ofHom ι)) := by
    exact (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ι)).2
      (fieldExtensionFaithfullyFlat ι) |>.2
  simpa [fieldRestrictionMap] using
    (MorphismProperty.cancel_right_of_respectsIso (P := @Surjective)
      (Spec.map (CommRingCat.ofHom ι)) eU.hom).2 hSpec

/-- The field-extension morphism on groupoid objects is flat. -/
theorem fieldRestriction_flat : Flat (fieldRestriction G eU ι).left := by
  change Flat (fieldRestrictionMap G eU ι)
  have hSpec : Flat (Spec.map (CommRingCat.ofHom ι)) := by
    exact (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ι)).2
      (fieldExtensionFaithfullyFlat ι) |>.1
  simpa [fieldRestrictionMap] using
    (MorphismProperty.cancel_right_of_respectsIso (P := @Flat)
      (Spec.map (CommRingCat.ofHom ι)) eU.hom).2 hSpec

/-- The field-extension morphism on groupoid objects is universally open. -/
theorem fieldRestriction_universallyOpen :
    UniversallyOpen (fieldRestriction G eU ι).left := by
  change UniversallyOpen (fieldRestrictionMap G eU ι)
  exact universallyOpenToFieldIso (fieldRestrictionMap G eU ι) eU

private lemma overPullbackFstProperty {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    {P : CategoryTheory.MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hg : P g.left) : P (pullback.fst f g).left := by
  rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_fst]
  exact (P.cancel_left_of_respectsIso
    (CategoryTheory.Limits.PreservesPullback.iso (Over.forget S) f g).hom
    (Limits.pullback.fst f.left g.left)).mpr (P.pullback_fst f.left g.left hg)

private lemma overPullbackSndProperty {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    {P : CategoryTheory.MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hf : P f.left) : P (pullback.snd f g).left := by
  rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_snd]
  exact (P.cancel_left_of_respectsIso
    (CategoryTheory.Limits.PreservesPullback.iso (Over.forget S) f g).hom
    (Limits.pullback.snd f.left g.left)).mpr (P.pullback_snd f.left g.left hf)

private lemma restrictedSourceOfStableUnderBaseChange
    {P : CategoryTheory.MorphismProperty Scheme.{u}} [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] {U' : Over S} (g : U' ⟶ G.U) (hs : P G.s.left) (hg : P g.left) :
    P (G.pullback g).s.left := by
  let Q : CategoryTheory.MorphismProperty (Over S) := P.inverseImage (Over.forget S)
  have hsPullback : P (Limits.pullback.snd G.s g).left :=
    overPullbackSndProperty G.s g hs
  have hgPullback : P (Limits.pullback.snd g G.t).left :=
    overPullbackSndProperty g G.t hg
  have hOuter :
      P (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t)).left :=
    overPullbackFstProperty (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) hgPullback
  have hComposite :
      Q
        ((pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.snd G.s g) := by
    have hProjected :
        Q
          (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
            Limits.pullback.snd G.s g) := by
      exact Q.comp_mem _ _ hOuter hsPullback
    exact (Q.cancel_left_of_respectsIso (pullbackArrowIso G g).hom
      (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.snd G.s g)).mpr hProjected
  have hCompositeLeft : P
      (((pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.snd G.s g).left) := by
    simpa [Q, MorphismProperty.inverseImage] using hComposite
  have hSource :
      (((pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.snd G.s g).left) = (G.pullback g).s.left := by
    simpa [AlgebraicGeometry.GroupoidScheme.pullback] using
      congrArg Over.Hom.left (pullbackArrowIso_hom_upper_snd G g)
  rw [hSource] at hCompositeLeft
  exact hCompositeLeft

private lemma restrictedTargetOfStableUnderBaseChange
    {P : CategoryTheory.MorphismProperty Scheme.{u}} [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] {U' : Over S} (g : U' ⟶ G.U) (ht : P G.t.left) (hg : P g.left) :
    P (G.pullback g).t.left := by
  let Q : CategoryTheory.MorphismProperty (Over S) := P.inverseImage (Over.forget S)
  have hgPullback : P (Limits.pullback.fst g G.t).left :=
    overPullbackFstProperty g G.t ht
  have hUpper : P (Limits.pullback.fst G.s g).left :=
    overPullbackFstProperty G.s g hg
  have hOuter :
      P (Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t)).left :=
    overPullbackSndProperty (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) hUpper
  have hComposite :
      Q
        ((pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst g G.t) := by
    have hProjected :
        Q
          (Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
            Limits.pullback.fst g G.t) := by
      exact Q.comp_mem _ _ hOuter hgPullback
    exact (Q.cancel_left_of_respectsIso (pullbackArrowIso G g).hom
      (Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.fst g G.t)).mpr hProjected
  have hCompositeLeft : P
      (((pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst g G.t).left) := by
    simpa [Q, MorphismProperty.inverseImage] using hComposite
  have hTarget :
      (((pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst g G.t).left) = (G.pullback g).t.left := by
    simpa [AlgebraicGeometry.GroupoidScheme.pullback] using
      congrArg Over.Hom.left (pullbackArrowIso_hom_lower_fst G g)
  rw [hTarget] at hCompositeLeft
  exact hCompositeLeft

private lemma pullbackToSourceSquare_eq_iteratedFst {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        pullback.fst (pullback.fst G.s g) (pullback.snd g G.t) =
      pullbackToSourceSquare G g := by
  apply pullback.hom_ext
  · calc
      (pullbackArrowIso G g).hom ≫
          pullback.fst (pullback.fst G.s g) (pullback.snd g G.t) ≫ pullback.fst G.s g =
        pullbackArrow G g := by
          simpa using pullbackArrowIso_hom_upper_fst G g
      _ = pullbackToSourceSquare G g ≫ pullback.fst G.s g := by
        simpa [pullbackToSourceSquare] using
          (Limits.pullback.lift_fst (pullbackArrow G g) (G.toPreRelation.pullback g).s
            (pullbackArrow_s G g)).symm
  · calc
      (pullbackArrowIso G g).hom ≫
          pullback.fst (pullback.fst G.s g) (pullback.snd g G.t) ≫ pullback.snd G.s g =
        (G.toPreRelation.pullback g).s := by
          simpa using pullbackArrowIso_hom_upper_snd G g
      _ = pullbackToSourceSquare G g ≫ pullback.snd G.s g := by
        simpa [pullbackToSourceSquare] using
          (Limits.pullback.lift_snd (pullbackArrow G g) (G.toPreRelation.pullback g).s
            (pullbackArrow_s G g)).symm

private lemma pullbackToTargetSquare_eq_iteratedSnd {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        pullback.snd (pullback.fst G.s g) (pullback.snd g G.t) =
      pullbackToTargetSquare G g := by
  apply pullback.hom_ext
  · calc
      (pullbackArrowIso G g).hom ≫
          pullback.snd (pullback.fst G.s g) (pullback.snd g G.t) ≫ pullback.fst g G.t =
        (G.toPreRelation.pullback g).t := by
          simpa using pullbackArrowIso_hom_lower_fst G g
      _ = pullbackToTargetSquare G g ≫ pullback.fst g G.t := by
        simpa [pullbackToTargetSquare] using
          (Limits.pullback.lift_fst (G.toPreRelation.pullback g).t (pullbackArrow G g)
            (pullbackToTargetSquare_condition G g)).symm
  · calc
      (pullbackArrowIso G g).hom ≫
          pullback.snd (pullback.fst G.s g) (pullback.snd g G.t) ≫ pullback.snd g G.t =
        pullbackArrow G g := by
          simpa using pullbackArrowIso_hom_lower_snd G g
      _ = pullbackToTargetSquare G g ≫ pullback.snd g G.t := by
        simpa [pullbackToTargetSquare] using
          (Limits.pullback.lift_snd (G.toPreRelation.pullback g).t (pullbackArrow G g)
            (pullbackToTargetSquare_condition G g)).symm

/-- The canonical map from the restricted arrows to the source pullback square is surjective. -/
theorem pullbackToSourceSquare_surjective :
    Surjective (pullbackToSourceSquare G (fieldRestriction G eU ι)).left := by
  let g := fieldRestriction G eU ι
  have hSnd : Surjective (pullback.snd g G.t).left := by
    exact overPullbackSndProperty g G.t
      (fieldRestriction_surjective (G := G) (eU := eU) (ι := ι))
  have hProj :
      Surjective (pullback.fst (pullback.fst G.s g) (pullback.snd g G.t)).left := by
    exact overPullbackFstProperty (pullback.fst G.s g) (pullback.snd g G.t) hSnd
  have hEq := congrArg (fun φ ↦ φ.left)
    (pullbackToSourceSquare_eq_iteratedFst (G := G) (g := g))
  rw [← hEq]
  exact MorphismProperty.RespectsIso.precomp (@Surjective) (pullbackArrowIso G g).hom.left _
    hProj

/-- The canonical map from the restricted arrows to the source pullback square is flat. -/
theorem pullbackToSourceSquare_flat :
    Flat (pullbackToSourceSquare G (fieldRestriction G eU ι)).left := by
  let g := fieldRestriction G eU ι
  have hSnd : Flat (pullback.snd g G.t).left := by
    exact overPullbackSndProperty g G.t
      (fieldRestriction_flat (G := G) (eU := eU) (ι := ι))
  have hProj : Flat (pullback.fst (pullback.fst G.s g) (pullback.snd g G.t)).left := by
    exact overPullbackFstProperty (pullback.fst G.s g) (pullback.snd g G.t) hSnd
  have hEq := congrArg (fun φ ↦ φ.left)
    (pullbackToSourceSquare_eq_iteratedFst (G := G) (g := g))
  rw [← hEq]
  exact MorphismProperty.RespectsIso.precomp (@Flat) (pullbackArrowIso G g).hom.left _ hProj

/-- The canonical map from the restricted arrows to the source pullback square is universally
open. -/
theorem pullbackToSourceSquare_universallyOpen :
    UniversallyOpen (pullbackToSourceSquare G (fieldRestriction G eU ι)).left := by
  let g := fieldRestriction G eU ι
  have hSnd : UniversallyOpen (pullback.snd g G.t).left := by
    exact overPullbackSndProperty g G.t
      (fieldRestriction_universallyOpen (G := G) (eU := eU) (ι := ι))
  have hProj :
      UniversallyOpen (pullback.fst (pullback.fst G.s g) (pullback.snd g G.t)).left := by
    exact overPullbackFstProperty (pullback.fst G.s g) (pullback.snd g G.t) hSnd
  have hEq := congrArg (fun φ ↦ φ.left)
    (pullbackToSourceSquare_eq_iteratedFst (G := G) (g := g))
  rw [← hEq]
  exact MorphismProperty.RespectsIso.precomp (@UniversallyOpen) (pullbackArrowIso G g).hom.left _
    hProj

/-- The canonical map from the restricted arrows to the target pullback square is surjective. -/
theorem pullbackToTargetSquare_surjective :
    Surjective (pullbackToTargetSquare G (fieldRestriction G eU ι)).left := by
  let g := fieldRestriction G eU ι
  have hFst : Surjective (pullback.fst G.s g).left := by
    exact overPullbackFstProperty G.s g
      (fieldRestriction_surjective (G := G) (eU := eU) (ι := ι))
  have hProj :
      Surjective (pullback.snd (pullback.fst G.s g) (pullback.snd g G.t)).left := by
    exact overPullbackSndProperty (pullback.fst G.s g) (pullback.snd g G.t) hFst
  have hEq := congrArg (fun φ ↦ φ.left)
    (pullbackToTargetSquare_eq_iteratedSnd (G := G) (g := g))
  rw [← hEq]
  exact MorphismProperty.RespectsIso.precomp (@Surjective) (pullbackArrowIso G g).hom.left _
    hProj

/-- The canonical map from the restricted arrows to the target pullback square is flat. -/
theorem pullbackToTargetSquare_flat :
    Flat (pullbackToTargetSquare G (fieldRestriction G eU ι)).left := by
  let g := fieldRestriction G eU ι
  have hFst : Flat (pullback.fst G.s g).left := by
    exact overPullbackFstProperty G.s g
      (fieldRestriction_flat (G := G) (eU := eU) (ι := ι))
  have hProj : Flat (pullback.snd (pullback.fst G.s g) (pullback.snd g G.t)).left := by
    exact overPullbackSndProperty (pullback.fst G.s g) (pullback.snd g G.t) hFst
  have hEq := congrArg (fun φ ↦ φ.left)
    (pullbackToTargetSquare_eq_iteratedSnd (G := G) (g := g))
  rw [← hEq]
  exact MorphismProperty.RespectsIso.precomp (@Flat) (pullbackArrowIso G g).hom.left _ hProj

/-- The canonical map from the restricted arrows to the target pullback square is universally
open. -/
theorem pullbackToTargetSquare_universallyOpen :
    UniversallyOpen (pullbackToTargetSquare G (fieldRestriction G eU ι)).left := by
  let g := fieldRestriction G eU ι
  have hFst : UniversallyOpen (pullback.fst G.s g).left := by
    exact overPullbackFstProperty G.s g
      (fieldRestriction_universallyOpen (G := G) (eU := eU) (ι := ι))
  have hProj :
      UniversallyOpen (pullback.snd (pullback.fst G.s g) (pullback.snd g G.t)).left := by
    exact overPullbackSndProperty (pullback.fst G.s g) (pullback.snd g G.t) hFst
  have hEq := congrArg (fun φ ↦ φ.left)
    (pullbackToTargetSquare_eq_iteratedSnd (G := G) (g := g))
  rw [← hEq]
  exact MorphismProperty.RespectsIso.precomp (@UniversallyOpen) (pullbackArrowIso G g).hom.left _
    hProj

/-- The source map of the field-restricted groupoid scheme is surjective. -/
theorem restrictionSource_surjective :
    Surjective (G.pullback (fieldRestriction G eU ι)).s.left := by
  exact restrictedSourceOfStableUnderBaseChange (G := G) (g := fieldRestriction G eU ι)
    (source_surjective_of_field G eU)
    (fieldRestriction_surjective (G := G) (eU := eU) (ι := ι))

/-- The source map of the field-restricted groupoid scheme is flat. -/
theorem restrictionSource_flat : Flat (G.pullback (fieldRestriction G eU ι)).s.left := by
  exact restrictedSourceOfStableUnderBaseChange (G := G) (g := fieldRestriction G eU ι)
    (source_flat_of_field G eU)
    (fieldRestriction_flat (G := G) (eU := eU) (ι := ι))

/-- The source map of the field-restricted groupoid scheme is universally open. -/
theorem restrictionSource_universallyOpen :
    UniversallyOpen (G.pullback (fieldRestriction G eU ι)).s.left := by
  exact restrictedSourceOfStableUnderBaseChange (G := G) (g := fieldRestriction G eU ι)
    (source_universallyOpen_of_field G eU)
    (fieldRestriction_universallyOpen (G := G) (eU := eU) (ι := ι))

/-- The target map of the field-restricted groupoid scheme is surjective. -/
theorem restrictionTarget_surjective :
    Surjective (G.pullback (fieldRestriction G eU ι)).t.left := by
  exact restrictedTargetOfStableUnderBaseChange (G := G) (g := fieldRestriction G eU ι)
    (target_surjective_of_field G eU)
    (fieldRestriction_surjective (G := G) (eU := eU) (ι := ι))

/-- The target map of the field-restricted groupoid scheme is flat. -/
theorem restrictionTarget_flat : Flat (G.pullback (fieldRestriction G eU ι)).t.left := by
  exact restrictedTargetOfStableUnderBaseChange (G := G) (g := fieldRestriction G eU ι)
    (target_flat_of_field G eU)
    (fieldRestriction_flat (G := G) (eU := eU) (ι := ι))

/-- The target map of the field-restricted groupoid scheme is universally open. -/
theorem restrictionTarget_universallyOpen :
    UniversallyOpen (G.pullback (fieldRestriction G eU ι)).t.left := by
  exact restrictedTargetOfStableUnderBaseChange (G := G) (g := fieldRestriction G eU ι)
    (target_universallyOpen_of_field G eU)
    (fieldRestriction_universallyOpen (G := G) (eU := eU) (ι := ι))

/-- The projection `R ×_{s, U} U' ⟶ R` in a field restriction is surjective. -/
theorem sourcePullbackFst_surjective :
    Surjective (pullback.fst G.s (fieldRestriction G eU ι)).left := by
  exact overPullbackFstProperty G.s (fieldRestriction G eU ι)
    (fieldRestriction_surjective (G := G) (eU := eU) (ι := ι))

/-- The projection `R ×_{s, U} U' ⟶ R` in a field restriction is flat. -/
theorem sourcePullbackFst_flat : Flat (pullback.fst G.s (fieldRestriction G eU ι)).left := by
  exact overPullbackFstProperty G.s (fieldRestriction G eU ι)
    (fieldRestriction_flat (G := G) (eU := eU) (ι := ι))

/-- The projection `R ×_{s, U} U' ⟶ R` in a field restriction is universally open. -/
theorem sourcePullbackFst_universallyOpen :
    UniversallyOpen (pullback.fst G.s (fieldRestriction G eU ι)).left := by
  exact overPullbackFstProperty G.s (fieldRestriction G eU ι)
    (fieldRestriction_universallyOpen (G := G) (eU := eU) (ι := ι))

/-- The projection `R ×_{s, U} U' ⟶ U'` in a field restriction is surjective. -/
theorem sourcePullbackSnd_surjective :
    Surjective (pullback.snd G.s (fieldRestriction G eU ι)).left := by
  exact overPullbackSndProperty G.s (fieldRestriction G eU ι)
    (source_surjective_of_field G eU)

/-- The projection `R ×_{s, U} U' ⟶ U'` in a field restriction is flat. -/
theorem sourcePullbackSnd_flat : Flat (pullback.snd G.s (fieldRestriction G eU ι)).left := by
  exact overPullbackSndProperty G.s (fieldRestriction G eU ι)
    (source_flat_of_field G eU)

/-- The projection `R ×_{s, U} U' ⟶ U'` in a field restriction is universally open. -/
theorem sourcePullbackSnd_universallyOpen :
    UniversallyOpen (pullback.snd G.s (fieldRestriction G eU ι)).left := by
  exact overPullbackSndProperty G.s (fieldRestriction G eU ι)
    (source_universallyOpen_of_field G eU)

/-- The projection `U' ×_{U, t} R ⟶ U'` in a field restriction is surjective. -/
theorem targetPullbackFst_surjective :
    Surjective (pullback.fst (fieldRestriction G eU ι) G.t).left := by
  exact overPullbackFstProperty (fieldRestriction G eU ι) G.t
    (target_surjective_of_field G eU)

/-- The projection `U' ×_{U, t} R ⟶ U'` in a field restriction is flat. -/
theorem targetPullbackFst_flat : Flat (pullback.fst (fieldRestriction G eU ι) G.t).left := by
  exact overPullbackFstProperty (fieldRestriction G eU ι) G.t
    (target_flat_of_field G eU)

/-- The projection `U' ×_{U, t} R ⟶ U'` in a field restriction is universally open. -/
theorem targetPullbackFst_universallyOpen :
    UniversallyOpen (pullback.fst (fieldRestriction G eU ι) G.t).left := by
  exact overPullbackFstProperty (fieldRestriction G eU ι) G.t
    (target_universallyOpen_of_field G eU)

/-- The projection `U' ×_{U, t} R ⟶ R` in a field restriction is surjective. -/
theorem targetPullbackSnd_surjective :
    Surjective (pullback.snd (fieldRestriction G eU ι) G.t).left := by
  exact overPullbackSndProperty (fieldRestriction G eU ι) G.t
    (fieldRestriction_surjective (G := G) (eU := eU) (ι := ι))

/-- The projection `U' ×_{U, t} R ⟶ R` in a field restriction is flat. -/
theorem targetPullbackSnd_flat : Flat (pullback.snd (fieldRestriction G eU ι) G.t).left := by
  exact overPullbackSndProperty (fieldRestriction G eU ι) G.t
    (fieldRestriction_flat (G := G) (eU := eU) (ι := ι))

/-- The projection `U' ×_{U, t} R ⟶ R` in a field restriction is universally open. -/
theorem targetPullbackSnd_universallyOpen :
    UniversallyOpen (pullback.snd (fieldRestriction G eU ι) G.t).left := by
  exact overPullbackSndProperty (fieldRestriction G eU ι) G.t
    (fieldRestriction_universallyOpen (G := G) (eU := eU) (ι := ι))

/-- The arrow component of the canonical morphism from a field restriction is surjective. -/
theorem pullbackHom_arrow_surjective :
    Surjective (G.pullbackHom (fieldRestriction G eU ι)).arrow.left := by
  let g := fieldRestriction G eU ι
  have hComp :
      (pullbackToSourceSquare G g).left ≫ (pullback.fst G.s g).left =
        (G.pullbackHom g).arrow.left := by
    simpa [pullbackToSourceSquare, pullbackHom, pullbackArrow] using
      congrArg Over.Hom.left
        (Limits.pullback.lift_fst (pullbackArrow G g) (G.toPreRelation.pullback g).s
          (pullbackArrow_s G g))
  rw [← hComp]
  exact CategoryTheory.MorphismProperty.comp_mem (@Surjective)
    (pullbackToSourceSquare G g).left (pullback.fst G.s g).left
    (pullbackToSourceSquare_surjective (G := G) (eU := eU) (ι := ι))
    (sourcePullbackFst_surjective (G := G) (eU := eU) (ι := ι))

/-- The arrow component of the canonical morphism from a field restriction is flat. -/
theorem pullbackHom_arrow_flat :
    Flat (G.pullbackHom (fieldRestriction G eU ι)).arrow.left := by
  let g := fieldRestriction G eU ι
  have hComp :
      (pullbackToSourceSquare G g).left ≫ (pullback.fst G.s g).left =
        (G.pullbackHom g).arrow.left := by
    simpa [pullbackToSourceSquare, pullbackHom, pullbackArrow] using
      congrArg Over.Hom.left
        (Limits.pullback.lift_fst (pullbackArrow G g) (G.toPreRelation.pullback g).s
          (pullbackArrow_s G g))
  rw [← hComp]
  exact @AlgebraicGeometry.Flat.comp _ _ _
    (pullbackToSourceSquare G g).left (pullback.fst G.s g).left
    (pullbackToSourceSquare_flat (G := G) (eU := eU) (ι := ι))
    (sourcePullbackFst_flat (G := G) (eU := eU) (ι := ι))

/-- The arrow component of the canonical morphism from a field restriction is universally
open. -/
theorem pullbackHom_arrow_universallyOpen :
    UniversallyOpen (G.pullbackHom (fieldRestriction G eU ι)).arrow.left := by
  let g := fieldRestriction G eU ι
  have hComp :
      (pullbackToSourceSquare G g).left ≫ (pullback.fst G.s g).left =
        (G.pullbackHom g).arrow.left := by
    simpa [pullbackToSourceSquare, pullbackHom, pullbackArrow] using
      congrArg Over.Hom.left
        (Limits.pullback.lift_fst (pullbackArrow G g) (G.toPreRelation.pullback g).s
          (pullbackArrow_s G g))
  rw [← hComp]
  exact CategoryTheory.MorphismProperty.comp_mem (@UniversallyOpen)
    (pullbackToSourceSquare G g).left (pullback.fst G.s g).left
    (pullbackToSourceSquare_universallyOpen (G := G) (eU := eU) (ι := ι))
    (sourcePullbackFst_universallyOpen (G := G) (eU := eU) (ι := ι))

/-- The arrow component of the canonical morphism from a field restriction is affine. -/
theorem pullbackHom_arrow_affine :
    IsAffineHom (G.pullbackHom (fieldRestriction G eU ι)).arrow.left := by
  let g := fieldRestriction G eU ι
  have hFieldAff : IsAffineHom g.left := by
    change IsAffineHom (fieldRestrictionMap G eU ι)
    simpa [fieldRestrictionMap] using
      (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom ι) ≫ eU.hom))
  have hSndAff : IsAffineHom (pullback.snd g G.t).left := by
    exact overPullbackSndProperty g G.t hFieldAff
  have hSquareAff : IsAffineHom (pullbackToSourceSquare G g).left := by
    have hProj : IsAffineHom (pullback.fst (pullback.fst G.s g) (pullback.snd g G.t)).left := by
      exact overPullbackFstProperty (pullback.fst G.s g) (pullback.snd g G.t) hSndAff
    have hEq := congrArg (fun φ ↦ φ.left)
      (pullbackToSourceSquare_eq_iteratedFst (G := G) (g := g))
    rw [← hEq]
    exact MorphismProperty.RespectsIso.precomp (@IsAffineHom) (pullbackArrowIso G g).hom.left _
      hProj
  have hFstAff : IsAffineHom (pullback.fst G.s g).left := by
    exact overPullbackFstProperty G.s g hFieldAff
  have hComp :
      (pullbackToSourceSquare G g).left ≫ (pullback.fst G.s g).left =
        (G.pullbackHom g).arrow.left := by
    simpa [pullbackToSourceSquare, pullbackHom, pullbackArrow] using
      congrArg Over.Hom.left
        (Limits.pullback.lift_fst (pullbackArrow G g) (G.toPreRelation.pullback g).s
          (pullbackArrow_s G g))
  rw [← hComp]
  exact @AlgebraicGeometry.instIsAffineHomCompScheme _ _ _
    (pullbackToSourceSquare G g).left (pullback.fst G.s g).left hSquareAff hFstAff

end FieldRestriction

end AlgebraicGeometry.GroupoidScheme
