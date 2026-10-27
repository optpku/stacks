/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Thickening
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Over

/-! # Reduction of directed affine thickening colimits -/

public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.AffineReduction

variable {S : Scheme.{u}}

/-- The empty scheme with its unique structure map to the base. -/
private abbrev emptyOver (S : Scheme.{u}) : Over S := Over.mk (Scheme.emptyTo S)

/-- The reduction of a selected affine stage, or the empty scheme for an empty index. -/
private def schemeFor {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) : Over S := by
  classical
  exact Over.reduction (if h : Nonempty Λ then D.obj (Classical.choice h) else emptyOver S)

/-- The empty sieve covers the empty scheme over the base in the fppf topology. -/
private theorem emptyCover :
    (⊥ : Sieve (emptyOver S)) ∈ (Scheme.fppfTopology.over S) (emptyOver S) := by
  rw [CategoryTheory.GrothendieckTopology.mem_over_iff, OrderIso.map_bot]
  change (⊥ : Sieve (∅ : Scheme.{u})) ∈ Scheme.fppfTopology (∅ : Scheme.{u})
  exact Scheme.bot_mem_grothendieckTopology _

/-- The section of a sheaf on the empty scheme obtained by empty-cover amalgamation. -/
private def emptySection (X : (Over S)ᵒᵖ ⥤ Type u)
    (hX : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X) : X.obj (op (emptyOver S)) :=
  ((isSheaf_iff_isSheaf_of_type _ _).mp hX _ emptyCover).amalgamate
    (fun _ _ h ↦ False.elim h) (by intro _ _ _ _ _ _ _ h; exact h.elim)

/-- The selected reduced stage maps into the sheaf through its supplied colimit comparison. -/
private def ιFor {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X)
    (hX : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X) :
    yoneda.obj (schemeFor D) ⟶ X := by
  classical
  unfold schemeFor
  split
  · exact yoneda.map (Over.reductionι _) ≫ c.ι.app _ ≫ η
  · exact yoneda.map (Over.reductionι _) ≫ yonedaEquiv.symm (emptySection X hX)

/-- Reductions of two stages are compared through a common upper stage. -/
private def stageCompare {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (i j : Λ) :
    Over.reduction (D.obj i) ⟶ Over.reduction (D.obj j) :=
  let k := (directed_of (· ≤ ·) i j).choose
  let fi := D.map (homOfLE (directed_of (· ≤ ·) i j).choose_spec.1)
  let fj := D.map (homOfLE (directed_of (· ≤ ·) i j).choose_spec.2)
  (@Over.reductionIsoOfThickening S (D.obj i) (D.obj k) fi
      (h.isThickening_map _)).hom ≫
    (@Over.reductionIsoOfThickening S (D.obj j) (D.obj k) fj
      (h.isThickening_map _)).inv

/-- Comparison of reduced stages is compatible with composition. -/
private theorem stageCompare_comp {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (i j k : Λ) :
    stageCompare D h i j ≫ stageCompare D h j k = stageCompare D h i k := sorry

/-- An element of the presheaf colimit is represented by an actual stage section. -/
private def representative {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) {T : Over S}
    (x : c.pt.obj (op T)) : Σ i, T ⟶ D.obj i :=
  let h := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op T)) hc) x
  ⟨h.choose, h.choose_spec.choose⟩

/-- The chosen representative maps to the original colimit section. -/
private theorem representative_spec {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) {T : Over S}
    (x : c.pt.obj (op T)) :
    (c.ι.app (representative D c hc x).1).app (op T)
      (representative D c hc x).2 = x :=
  (Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op T)) hc) x).choose_spec.choose_spec

/-- A stage representative of a section coming from a reduced algebraic space kills the
stage nilradical. -/
private theorem stageFactor_nilradical_le_ker
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T))
    (i : Λ) (a : T ⟶ D.obj i)
    (ha : η.app (op T) ((c.ι.app i).app (op T) a) = f.app (op T) x) :
    (D.obj i).left.nilradical ≤ a.left.ker := sorry

/-- A reduced-stage section is transported to the selected reduced stage. -/
private def toSelectedStage {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (i : Λ) :
    Over.reduction (D.obj i) ⟶ schemeFor D := by
  classical
  unfold schemeFor
  split
  · exact stageCompare D h i _
  · exact False.elim (‹¬ Nonempty Λ› ⟨i⟩)

/-- Local colimit preimages give concrete sections of the selected reduced stage. -/
private def localFamily {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T)) :
    Presieve.FamilyOfElements (yoneda.obj (schemeFor D))
      (Presheaf.imageSieve η (f.app (op T) x)).arrows := fun V g hg ↦
  let y := Presheaf.localPreimage η (f.app (op T) x) g hg
  let a := representative D c hc y
  let ha : η.app (op V) ((c.ι.app a.1).app (op V) a.2) =
      f.app (op V) (G.functorOfPoints.map g.op x) := by
    rw [representative_spec, Presheaf.app_localPreimage]
    exact (NatTrans.naturality_apply f g.op x).symm
  let hk := stageFactor_nilradical_le_ker D h c hc η hηsurj hη G hG f
    (G.functorOfPoints.map g.op x) a.1 a.2 ha
  let b : V ⟶ Over.reduction (D.obj a.1) :=
    Over.homMk ((D.obj a.1).left.nilradical.lift a.2.left hk) (by
      change (D.obj a.1).left.nilradical.lift a.2.left hk ≫
        ((D.obj a.1).left.nilradical.subschemeι ≫ (D.obj a.1).hom) = V.hom
      rw [← Category.assoc, Scheme.IdealSheafData.lift_subschemeι]
      exact a.2.w)
  b ≫ toSelectedStage D h a.1

/-- The local reduced-stage sections agree on overlaps. -/
private theorem localFamily_compatible
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T)) :
    (localFamily D h c hc η hηsurj hη G hG f x).Compatible := sorry

/-- The lift on sections amalgamates the concrete reduced-stage family. -/
private def liftApp {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hηinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T)) :
    T ⟶ schemeFor D :=
  (CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology.over S) (yoneda.obj (schemeFor D)) _
      (hηsurj.imageSieve_mem (f.app (op T) x))).amalgamate
    (localFamily D h c hc η hηsurj hηinj G hG f x)
    (localFamily_compatible D h c hc η hηsurj hηinj G hG f x)

/-- The amalgamated lift commutes with restriction of sections. -/
private theorem lift_naturality
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hηinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T V : (Over S)ᵒᵖ} (g : T ⟶ V) :
    G.functorOfPoints.map g ≫
        TypeCat.ofHom (liftApp D h c hc η hηsurj hηinj G hG f) =
      TypeCat.ofHom (liftApp D h c hc η hηsurj hηinj G hG f) ≫
        (yoneda.obj (schemeFor D)).map g := sorry

/-- A map from a reduced algebraic space lifts by the pointwise sheaf-gluing construction. -/
private def liftFor {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hηinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) : G.functorOfPoints ⟶ yoneda.obj (schemeFor D) where
  app T := TypeCat.ofHom (liftApp D h c hc η hηsurj hηinj G hG f)
  naturality _ _ g := lift_naturality D h c hc η hηsurj hηinj G hG f g

/-- The inclusion uses the cocone and local comparison supplied by the affine presentation. -/
private def ιFromPresentation {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) : yoneda.obj (schemeFor D) ⟶ X :=
  ιFor D h.exists_colimit.choose h.exists_colimit.choose_spec.choose h.isSheaf

/-- The lift uses the colimit evidence and local comparison supplied by the presentation. -/
private def liftFromPresentation {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) : G.functorOfPoints ⟶ yoneda.obj (schemeFor D) :=
  let c := h.exists_colimit.choose
  let η := h.exists_colimit.choose_spec.choose
  let hc := h.exists_colimit.choose_spec.choose_spec
  liftFor D h c (Classical.choice hc.1) η hc.2.1 hc.2.2 G hG f

variable {X : (Over S)ᵒᵖ ⥤ Type u}
variable (hX : ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
  (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D X)

/-- The index chosen from the supplied affine presentation. -/
private abbrev index : Type u := hX.choose

/-- The order belonging to the chosen presentation index. -/
private abbrev indexOrder : Preorder (index hX) := hX.choose_spec.choose

/-- Directedness belonging to the chosen presentation index. -/
private theorem indexDirected :
    @IsDirected (index hX) (@LE.le (index hX) (indexOrder hX).toLE) :=
  hX.choose_spec.choose_spec.choose

/-- The diagram chosen from the supplied presentation hypothesis. -/
private def diagram :
    @CategoryTheory.Functor (index hX) (@Preorder.smallCategory _ (indexOrder hX))
      (Over S) inferInstance :=
  hX.choose_spec.choose_spec.choose_spec.choose

/-- The chosen diagram retains its supplied affine thickening and colimit properties. -/
private theorem presentation :
    @IsDirectedAffineThickeningColimit S (index hX) (indexOrder hX) (indexDirected hX)
      (diagram hX) X :=
  hX.choose_spec.choose_spec.choose_spec.choose_spec

/-- The reduction of a selected affine stage of a directed affine thickening presentation,
with the empty scheme when the index is empty. -/
def scheme : Over S := @schemeFor S (index hX) (indexOrder hX) (diagram hX)

/-- The inclusion of the selected stage reduction into the affine formal algebraic space. -/
def ι : yoneda.obj (scheme hX) ⟶ X :=
  @ιFromPresentation S (index hX) (indexOrder hX) (indexDirected hX)
    (diagram hX) X (presentation hX)

/-- The selected stage reduction is an affine scheme. -/
theorem scheme_isAffine : IsAffine (scheme hX).left := by
  classical
  unfold scheme schemeFor
  split
  · exact (@IsClosedImmersion.isAffine_surjective_of_isAffine _ _
      ((presentation hX).isAffine_obj _) (Scheme.reductionι _)
      (Scheme.isClosedImmersion_reductionι _)).1
  · exact (@IsClosedImmersion.isAffine_surjective_of_isAffine _ _
      (inferInstance : IsAffine (∅ : Scheme.{u})) (Scheme.reductionι _)
      (Scheme.isClosedImmersion_reductionι _)).1

/-- The selected stage reduction is reduced. -/
theorem scheme_isReduced : IsReduced (scheme hX).left :=
  Scheme.instIsReducedReduction _

/-- Every morphism from a reduced algebraic space into the affine formal algebraic space
has a specified lift to its selected affine reduction. -/
def lift (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) : G.functorOfPoints ⟶ yoneda.obj (scheme hX) :=
  @liftFromPresentation S (index hX) (indexOrder hX) (indexDirected hX)
    (diagram hX) X (presentation hX) G hG f

/-- The specified reduction lift followed by the inclusion is the original morphism. -/
theorem lift_fac (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) : lift hX G hG f ≫ ι hX = f := sorry

/-- Every factorization through the selected affine reduction equals the specified lift. -/
theorem lift_unique (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) (g : G.functorOfPoints ⟶ yoneda.obj (scheme hX))
    (hg : g ≫ ι hX = f) : g = lift hX G hG f := sorry

/-- The specified affine reduction lift satisfies factorization and uniqueness together. -/
theorem spec (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) :
    lift hX G hG f ≫ ι hX = f ∧
      ∀ g : G.functorOfPoints ⟶ yoneda.obj (scheme hX),
        g ≫ ι hX = f → g = lift hX G hG f :=
  ⟨lift_fac hX G hG f, fun g hg ↦ lift_unique hX G hG f g hg⟩

end AlgebraicGeometry.FormalAlgebraicSpace.AffineReduction
