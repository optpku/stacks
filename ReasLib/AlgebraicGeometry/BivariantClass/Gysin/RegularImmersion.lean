/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.NormalSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Gysin

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- The conormal sheaf of a regular immersion is finite locally free. -/
@[instance]
theorem conormalSheaf_isFiniteLocallyFree {X P : Scheme.{u}}
    (i : X ⟶ P) [IsRegularImmersion i] :
    Scheme.Modules.IsFiniteLocallyFree (conormalSheaf i) := sorry

/-- The normal sheaf of a regular immersion is finite locally free. -/
@[instance]
theorem normalSheaf_isFiniteLocallyFree {X P : Scheme.{u}}
    (i : X ⟶ P) [IsRegularImmersion i] :
    Scheme.Modules.IsFiniteLocallyFree (normalSheaf i) := by
  apply (SheafOfModules.IsFiniteLocallyFree.iff_of_iso
    ((CategoryTheory.ihom (conormalSheaf i)).mapIso
      (RingedSpace.unitIsoTensorUnit X.toRingedSpace))).mpr
  exact @Scheme.Modules.IsFiniteLocallyFree.dual X (conormalSheaf i)
    (conormalSheaf_isFiniteLocallyFree i)

/-- The normal sheaf with its bidual identification is a virtual normal bundle, without
any assumption of globally constant rank. -/
def normalBundle {X P : Scheme.{u}} (i : X ⟶ P) [IsRegularImmersion i]
    (e : Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i) :
    VirtualNormalBundle i :=
  ofSurjection i (normalSheaf i) (normalSheaf_isFiniteLocallyFree i) e.hom inferInstance

/-- The module of the normal virtual bundle is the normal sheaf. -/
theorem normalBundle_module {X P : Scheme.{u}} (i : X ⟶ P) [IsRegularImmersion i]
    (e : Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i) :
    (normalBundle i e).module = normalSheaf i := rfl

/-- The quotient map of the normal virtual bundle is the chosen bidual identification. -/
theorem normalBundle_map {X P : Scheme.{u}} (i : X ⟶ P) [IsRegularImmersion i]
    (e : Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i) :
    (normalBundle i e).map = e.hom := rfl

/-- The degree-`r` Gysin coefficient of a regular immersion is the normal-sheaf class of
its canonical closed factor followed by degree-zero open flat pullback. -/
def immersionClassDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) [IsRegularImmersion i.left]
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    (r : ℕ) : BivariantClass δ i (r : ℤ) := by
  have c := comp δ
    (overHom X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i))
    (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl)
    (globalClassOfRank δ X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder D r)
    (@flatPullback _ _ δ _ _ _ _ _
      (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl) 0
      (by change Flat i.left.coborderRange.ι; infer_instance)
      (relativeDimension_zero_of_isOpenImmersion i.left.coborderRange.ι))
  have hcomp : overHom X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i) ≫
      overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl = i := by
    calc
      _ = overHom X.hom P.hom i.left (Over.w i) := by
        apply Over.OverMorphism.ext
        exact i.left.liftCoborder_ι
      _ = i := by
        unfold overHom
        exact Over.homMk_eta i (Over.w i)
  rw [hcomp] at c
  simp only [Nat.cast_zero, neg_zero, add_zero] at c
  convert c using 0
  rfl

/-- Restricting an immersion coefficient to its rank locus gives the composition of the
closed rank class with the degree-zero open pullback. -/
theorem immersionClassDegree_component
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) [IsRegularImmersion i.left]
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    (r : ℕ) :
    ComponentRestriction.restrict δ i (r : ℤ)
        (rankOpen i.left (normalBundle i.left e) r) ⊤ (by simp)
        (immersionClassDegree δ i e D r) =
      (by
        have c := comp δ
          (ClosedDeformation.rankHom X.hom (i.left.coborderRange.ι ≫ P.hom)
            i.left.liftCoborder
            (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
            (normalBundle i.left e).toCoborder r)
          (ComponentRestriction.hom
            (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl)
            ⊤ ⊤ (by simp))
          (closedClassOfRank δ X.hom (i.left.coborderRange.ι ≫ P.hom)
            i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder D r)
          (ComponentRestriction.restrict δ
            (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl)
            0 ⊤ ⊤ (by simp)
            (@flatPullback _ _ δ _ _ _ _ _
              (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl) 0
              (by change Flat i.left.coborderRange.ι; infer_instance)
              (relativeDimension_zero_of_isOpenImmersion i.left.coborderRange.ι)))
        dsimp only [ClosedDeformation.rankHom, VirtualNormalBundle.toCoborder] at c
        rw [factorizationRestrictionHom_eq X.hom P.hom i.left (Over.w i)
          i.left.liftCoborder i.left.coborderRange.ι i.left.liftCoborder_ι
          (normalBundle i.left e) r, add_zero] at c
        have h : overHom X.hom P.hom i.left (Over.w i) = i := by
          unfold overHom
          exact Over.homMk_eta i (Over.w i)
        rw [h] at c
        convert c using 0
        rfl) := sorry

end AlgebraicGeometry.BivariantClass.Gysin

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- The closed coborder factor of a section, as a morphism over `S`. -/
noncomputable def sectionCoborderClosed
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    Over.mk X.hom ⟶ Over.mk (s.left.coborderRange.ι ≫ P.hom) :=
  overHom X.hom (s.left.coborderRange.ι ≫ P.hom) s.left.liftCoborder
    (factorization_over X.hom P.hom s.left s.w
      s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)

/-- `sectionCoborderClosed` is the virtual-normal `overHom` of the coborder closed immersion. -/
theorem sectionCoborderClosed_def
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    sectionCoborderClosed s =
      overHom X.hom (s.left.coborderRange.ι ≫ P.hom) s.left.liftCoborder
        (factorization_over X.hom P.hom s.left s.w
          s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι) := sorry

/-- The open coborder factor of a section, as a morphism over `S`. -/
noncomputable def sectionCoborderOpen
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    Over.mk (s.left.coborderRange.ι ≫ P.hom) ⟶ Over.mk P.hom :=
  overHom (s.left.coborderRange.ι ≫ P.hom) P.hom s.left.coborderRange.ι rfl

/-- `sectionCoborderOpen` is the virtual-normal `overHom` of the coborder open immersion. -/
theorem sectionCoborderOpen_def
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    sectionCoborderOpen s =
      overHom (s.left.coborderRange.ι ≫ P.hom) P.hom s.left.coborderRange.ι rfl := sorry

/-- The underlying scheme morphism of `sectionCoborderOpen` is an open immersion. -/
instance sectionCoborderOpen_isOpenImmersion
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    IsOpenImmersion (sectionCoborderOpen s).left := sorry

/-- The coborder closed-open factorization of a section recovers the virtual-normal packaging of
the section. -/
theorem gysinSection_factorization
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    sectionCoborderClosed s ≫ sectionCoborderOpen s =
      overHom X.hom P.hom s.left s.w := sorry

/-- The canonical `Over.mk` isomorphisms form a pullback square against a section and its
coborder factorization. -/
theorem sectionCoborder_conj_isPullback {S : Scheme.{u}} {X P : Over S}
    (s : X ⟶ P) [IsImmersion s.left] :
    IsPullback (overMkIso X).inv.left s.left
      (sectionCoborderClosed s ≫ sectionCoborderOpen s).left
      (overMkIso P).inv.left := sorry

/-- The Gysin class of a section as a class of `s : X ⟶ P`: coborder composition on `Over.mk`,
conjugated along `overMkIso`. -/
noncomputable def gysinSection
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [IsImmersion s.left] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf s.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf s.left) ≅
      Scheme.Hom.conormalSheaf s.left)
    (D : ClosedDeformation X.hom (s.left.coborderRange.ι ≫ P.hom)
      s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheaf s.left r e).toCoborder) :
    BivariantClass δ s (r : ℤ) :=
  Nonnegative.castGrading δ
      ((congrArg ((r : ℤ) + ·) neg_zero).trans (add_zero (r : ℤ)))
    (restrict δ (overMkIso X).inv s (overMkIso P).inv
      (sectionCoborder_conj_isPullback s) ((r : ℤ) + (-(0 : ℤ)))
      (comp δ (sectionCoborderClosed s) (sectionCoborderOpen s)
        (globalClassOfRank δ X.hom (s.left.coborderRange.ι ≫ P.hom)
          s.left.liftCoborder
          (factorization_over X.hom P.hom s.left s.w
            s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
          (ofNormalSheaf s.left r e).toCoborder D r)
        (flatPullback δ (sectionCoborderOpen s) 0)))

/-- `gysinSection` is the degree-`r` conjugate of the coborder closed class of the normal sheaf
composed with degree-zero open pullback. -/
theorem gysinSection_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [IsImmersion s.left] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf s.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf s.left) ≅
      Scheme.Hom.conormalSheaf s.left)
    (D : ClosedDeformation X.hom (s.left.coborderRange.ι ≫ P.hom)
      s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheaf s.left r e).toCoborder) :
    gysinSection δ s r e D =
      Nonnegative.castGrading δ
          ((congrArg ((r : ℤ) + ·) neg_zero).trans (add_zero (r : ℤ)))
        (restrict δ (overMkIso X).inv s (overMkIso P).inv
          (sectionCoborder_conj_isPullback s) ((r : ℤ) + (-(0 : ℤ)))
          (comp δ (sectionCoborderClosed s) (sectionCoborderOpen s)
            (globalClassOfRank δ X.hom (s.left.coborderRange.ι ≫ P.hom)
              s.left.liftCoborder
              (factorization_over X.hom P.hom s.left s.w
                s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
              (ofNormalSheaf s.left r e).toCoborder D r)
            (flatPullback δ (sectionCoborderOpen s) 0))) := sorry

end AlgebraicGeometry.BivariantClass

namespace AlgebraicGeometry.BivariantClass.Gysin

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- A chosen deformation to the normal cone of the closed coborder factor of an immersion,
with the canonical normal virtual bundle and arbitrary locally varying rank. -/
abbrev NormalSpecializationOfRankLoci
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left]
    [Scheme.Modules.IsFiniteLocallyFree (conormalSheaf s.left)] :=
  ClosedDeformation X.hom (s.left.coborderRange.ι ≫ P.hom) s.left.liftCoborder
    (factorization_over X.hom P.hom s.left s.w
      s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
    (ofNormalSheafOfRankLoci s.left).toCoborder

/-- The completed normal Gysin class of an immersion, formed on its clopen normal-rank
loci by closed deformation followed by open flat pullback. -/
def normalCompletedClassOfRankLoci
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [IsImmersion s.left]
    [Scheme.Modules.IsFiniteLocallyFree (conormalSheaf s.left)]
    (D : NormalSpecializationOfRankLoci s) :
    CompletedClass δ X.hom P.hom s.left s.w (ofNormalSheafOfRankLoci s.left) :=
  composeClasses δ X.hom P.hom s.left s.w s.left.liftCoborder
    s.left.coborderRange.ι s.left.liftCoborder_ι (ofNormalSheafOfRankLoci s.left)
    (closedClass δ X.hom (s.left.coborderRange.ι ≫ P.hom) s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheafOfRankLoci s.left).toCoborder D)

end AlgebraicGeometry.BivariantClass.Gysin

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle Gysin

/-- The global degree-`r` normal Gysin coefficient of an immersion, glued from its
completed class on the clopen normal-rank loci with canonical biduality. -/
def gysinSectionOfRankLoci
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [h_s : IsImmersion s.left]
    [Scheme.Modules.IsFiniteLocallyFree (conormalSheaf s.left)]
    (D : NormalSpecializationOfRankLoci s) (r : ℕ) : BivariantClass δ s (r : ℤ) :=
  cast (congrArg (fun f : X ⟶ P ↦ BivariantClass δ f (r : ℤ)) (overHom_eq_over s))
    (((OpenRestriction.Completion.globalEquiv δ (overHom X.hom P.hom s.left s.w)
      (rankOpen (Z := X.left) (X := P.left) s.left (ofNormalSheafOfRankLoci s.left))
      (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
      (@Scheme.Modules.rankClopen_iSup X.left
        (ofNormalSheafOfRankLoci s.left).module
        (ofNormalSheafOfRankLoci s.left).isFiniteLocallyFree)
      (by simp)
      (@Scheme.Modules.rankClopen_pairwiseDisjoint X.left
        (ofNormalSheafOfRankLoci s.left).module
        (ofNormalSheafOfRankLoci s.left).isFiniteLocallyFree)
      (by intro a b h; exact (h (Subsingleton.elim a b)).elim)
      (fun n ↦ (@Scheme.Modules.rankClopen X.left
        (ofNormalSheafOfRankLoci s.left).module
        (ofNormalSheafOfRankLoci s.left).isFiniteLocallyFree n).isClopen)
      (fun _ ↦ isClopen_univ)
      (rankOpen_le_preimage_top X.hom P.hom s.left s.w
        (ofNormalSheafOfRankLoci s.left)))
      (normalCompletedClassOfRankLoci δ s D)).1 r)

/-- Restricting a global normal Gysin coefficient to a clopen normal-rank locus recovers
that coefficient of the completed normal Gysin class. -/
theorem gysinSectionOfRankLoci_component
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [h_s : IsImmersion s.left]
    [Scheme.Modules.IsFiniteLocallyFree (conormalSheaf s.left)]
    (D : NormalSpecializationOfRankLoci s) (n r : ℕ) :
    ComponentRestriction.restrict δ (overHom X.hom P.hom s.left s.w) (r : ℤ)
        (rankOpen (Z := X.left) (X := P.left) s.left (ofNormalSheafOfRankLoci s.left) n) ⊤
        (rankOpen_le_preimage_top X.hom P.hom s.left s.w
          (ofNormalSheafOfRankLoci s.left) n)
        (cast (congrArg (fun f : X ⟶ P ↦ BivariantClass δ f (r : ℤ))
          (overHom_eq_over s).symm) (gysinSectionOfRankLoci δ s D r)) =
      normalCompletedClassOfRankLoci δ s D n r := sorry

/-- Normal Gysin coefficients do not depend on the chosen model of deformation to the
normal cone. -/
theorem gysinSectionOfRankLoci_independent
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [IsImmersion s.left]
    [Scheme.Modules.IsFiniteLocallyFree (conormalSheaf s.left)]
    (D D' : NormalSpecializationOfRankLoci s) (r : ℕ) :
    gysinSectionOfRankLoci δ s D r = gysinSectionOfRankLoci δ s D' r := sorry

/-- When the conormal sheaf has constant rank `r`, the canonical normal Gysin family
is concentrated in degree `r` and agrees there with its fixed-rank construction. -/
theorem gysinSectionOfRankLoci_eq_ofRank
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [IsImmersion s.left] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf s.left)]
    (D : NormalSpecializationOfRankLoci s) :
    gysinSectionOfRankLoci δ s D r =
        gysinSection δ s r (bidualityIsoOfRankLoci s.left) D ∧
      ∀ n : ℕ, n ≠ r → gysinSectionOfRankLoci δ s D n =
        pointwiseZero δ s (n : ℤ) := sorry

end AlgebraicGeometry.BivariantClass
