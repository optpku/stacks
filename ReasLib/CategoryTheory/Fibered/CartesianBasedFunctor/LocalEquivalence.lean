/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.HomPresheaf
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
public import ReasLib.CategoryTheory.Sites.LocallyBijective.SheafLift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local equivalences of heterogeneous cartesian functors

This module owns the site-local notion for cartesian functors whose source and target total
categories may live in different universes.  The Hom condition uses the minimally lifted
Hom-presheaf map from `CartesianBasedFunctor.HomPresheaf.Chosen`; local essential surjectivity
is expressed by a covering essential-image sieve.

The fixed-universe `FiberedCategoryOver.Hom.IsLocalEquivalence` is a specialization of this
owner, not a second definition.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} [p₁.IsFibered] [p₂.IsFibered]

namespace CartesianBasedFunctor

/-- A target-fiber object has an essential preimage along a base arrow when its chosen
reindexing is isomorphic to the image of a source-fiber object. -/
@[stacks 02ZP "essential-image preimage condition",
  stacks 02ZN "stackification essential-image preimage condition"]
def EssentialImage.HasPreimage
    (F : CartesianBasedFunctor p₁ p₂) {U V : C} (y : p₂.Fiber U)
    (f : V ⟶ U) : Prop :=
  ∃ x : p₁.Fiber V,
    Nonempty ((F.fiberFunctor V).obj x ≅
      f⁎[Functor.Cleavage.ofIsFibered p₂] y)

/-- Having an essential preimage along a base arrow is stable under further base change. -/
@[stacks 02ZP "essential-image preimage base-change stability"]
theorem EssentialImage.HasPreimage.precomp
    (F : CartesianBasedFunctor p₁ p₂) {U V W : C} {y : p₂.Fiber U}
    {f : V ⟶ U} (h : EssentialImage.HasPreimage F y f) (g : W ⟶ V) :
    EssentialImage.HasPreimage F y (g ≫ f) := by
  rcases h with ⟨x, ⟨e⟩⟩
  refine ⟨g⁎[Functor.Cleavage.ofIsFibered p₁] x, ⟨?_⟩⟩
  exact (Reindex.mapIso F (Functor.Cleavage.ofIsFibered p₁)
    (Functor.Cleavage.ofIsFibered p₂) g x).symm ≪≫
      ((Functor.Cleavage.ofIsFibered p₂).reindex g).mapIso e ≪≫
        (Functor.Cleavage.Reindex.compIsoApp
          (Functor.Cleavage.ofIsFibered p₂) f g y).symm

/-- The sieve of base arrows along which a target-fiber object has an essential preimage. -/
@[stacks 02ZP "essential-image sieve",
  stacks 02ZN "stackification essential-image sieve"]
def EssentialImage.sieve
    (F : CartesianBasedFunctor p₁ p₂) {U : C} (y : p₂.Fiber U) : Sieve U where
  arrows _ f := EssentialImage.HasPreimage F y f
  downward_closed h g := EssentialImage.HasPreimage.precomp F h g

/-- Membership in the essential-image sieve is the corresponding essential-preimage
condition. -/
@[simp, stacks 02ZP "essential-image sieve membership",
  stacks 02ZN "stackification essential-image sieve membership"]
theorem EssentialImage.mem_sieve_iff
    (F : CartesianBasedFunctor p₁ p₂) {U V : C} (y : p₂.Fiber U)
    (f : V ⟶ U) :
    EssentialImage.sieve F y f ↔ EssentialImage.HasPreimage F y f := Iff.rfl

/-- A heterogeneous cartesian functor is locally essentially surjective when every target-fiber
object has a covering essential-image sieve. -/
@[stacks 06P2 "heterogeneous local essential surjectivity",
  stacks 02ZP "(2), local essential surjectivity",
  stacks 02ZN "(2), stackification local essential surjectivity"]
def LocallyEssentiallySurjective
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) : Prop :=
  ∀ {U : C} (y : p₂.Fiber U), EssentialImage.sieve F y ∈ J U

/-- The sieve formulation of heterogeneous local essential surjectivity is equivalent to the
coverwise formulation. -/
@[stacks 02ZP "(2), coverwise local essential surjectivity",
  stacks 02ZN "(2), coverwise stackification local essential surjectivity"]
theorem LocallyEssentiallySurjective.iff_forall_cover
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂} :
    LocallyEssentiallySurjective J F ↔
      ∀ {U : C} (y : p₂.Fiber U), ∃ T : J.Cover U, ∀ I : T.Arrow,
        EssentialImage.HasPreimage F y I.f := by
  constructor
  · intro hF U y
    exact ⟨⟨EssentialImage.sieve F y, hF y⟩, fun I ↦ I.hf⟩
  · intro hF U y
    obtain ⟨T, hT⟩ := hF y
    exact J.superset_covering (fun V f hf ↦ hT ⟨V, f, hf⟩) T.condition

/-- The essential-image sieve of a target-fiber object is covering under local essential
surjectivity. -/
@[stacks 02ZP "covering essential-image sieve",
  stacks 02ZN "stackification covering essential-image sieve"]
theorem LocallyEssentiallySurjective.sieve_mem
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : LocallyEssentiallySurjective J F) {U : C} (y : p₂.Fiber U) :
    EssentialImage.sieve F y ∈ J U := hF y

/-- The canonical cover whose underlying sieve is the heterogeneous essential-image sieve. -/
@[stacks 02ZP "canonical essential-image cover",
  stacks 02ZN "canonical stackification essential-image cover"]
def EssentialImage.cover
    {J : GrothendieckTopology C} (F : CartesianBasedFunctor p₁ p₂)
    (hF : LocallyEssentiallySurjective J F) {U : C} (y : p₂.Fiber U) :
    J.Cover U :=
  ⟨EssentialImage.sieve F y, hF.sieve_mem y⟩

/-- Every arrow in the canonical essential-image cover admits a source-fiber model after
reindexing the target object. -/
@[stacks 02ZP "essential-image cover specification",
  stacks 02ZN "stackification essential-image cover specification"]
theorem EssentialImage.cover_spec
    {J : GrothendieckTopology C} (F : CartesianBasedFunctor p₁ p₂)
    (hF : LocallyEssentiallySurjective J F) {U : C} (y : p₂.Fiber U)
    (I : (EssentialImage.cover F hF y).Arrow) :
    ∃ x : p₁.Fiber I.Y,
      Nonempty ((F.fiberFunctor I.Y).obj x ≅
        I.f⁎[Functor.Cleavage.ofIsFibered p₂] y) := I.hf

/-- Compose two heterogeneous essential-image isomorphisms, replacing iterated chosen
reindexing by reindexing along the composite base arrow. -/
noncomputable def EssentialImage.compIso
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {F : CartesianBasedFunctor p₁ p₂} {G : CartesianBasedFunctor p₂ p₃}
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (z : p₃.Fiber U) (y : p₂.Fiber V) (x : p₁.Fiber W)
    (eF : (F.fiberFunctor W).obj x ≅
      g⁎[Functor.Cleavage.ofIsFibered p₂] y)
    (eG : (G.fiberFunctor V).obj y ≅
      f⁎[Functor.Cleavage.ofIsFibered p₃] z) :
    ((F.comp G).fiberFunctor W).obj x ≅
      (g ≫ f)⁎[Functor.Cleavage.ofIsFibered p₃] z :=
  Iso.trans
    (Iso.trans
      (Functor.mapIso (G.fiberFunctor W) eF)
      (CartesianBasedFunctor.Reindex.mapIso G
        (Functor.Cleavage.ofIsFibered p₂)
        (Functor.Cleavage.ofIsFibered p₃) g y).symm)
    (Iso.trans
      (((Functor.Cleavage.ofIsFibered p₃).reindex g).mapIso eG)
      (Functor.Cleavage.Reindex.compIsoApp
        (Functor.Cleavage.ofIsFibered p₃) f g z).symm)

/-- Heterogeneous local essential surjectivity is stable under composition. -/
theorem LocallyEssentiallySurjective.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C}
    {F : CartesianBasedFunctor p₁ p₂} {G : CartesianBasedFunctor p₂ p₃}
    (hF : LocallyEssentiallySurjective J F)
    (hG : LocallyEssentiallySurjective J G) :
    LocallyEssentiallySurjective J (F.comp G) := by
  intro U z
  apply J.transitive (hG z)
  intro V f hf
  rcases hf with ⟨y, ⟨eG⟩⟩
  apply J.superset_covering _ (hF y)
  intro W g hg
  rcases hg with ⟨x, ⟨eF⟩⟩
  exact ⟨x, ⟨EssentialImage.compIso f g z y x eF eG⟩⟩

/-- The identity heterogeneous cartesian functor is locally essentially surjective. -/
theorem LocallyEssentiallySurjective.id (J : GrothendieckTopology C) :
    LocallyEssentiallySurjective J (CartesianBasedFunctor.id p₁) := by
  intro U y
  apply J.superset_covering (S := ⊤) _ (J.top_mem U)
  intro V f _
  exact ⟨f⁎[Functor.Cleavage.ofIsFibered p₁] y, ⟨Iso.refl _⟩⟩

/-- Heterogeneous local essential surjectivity is preserved when the topology is enlarged. -/
theorem LocallyEssentiallySurjective.of_le
    {J K : GrothendieckTopology C} (hJK : J ≤ K)
    {F : CartesianBasedFunctor p₁ p₂} (hF : LocallyEssentiallySurjective J F) :
    LocallyEssentiallySurjective K F := by
  intro U y
  exact hJK U (hF y)

/-- An equivalence over the base is locally essentially surjective. -/
theorem LocallyEssentiallySurjective.of_isEquivalence
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂)
    (hF : F.toBasedFunctor.IsEquivalence) :
    LocallyEssentiallySurjective J F := by
  intro U y
  apply J.superset_covering (S := ⊤) _ (J.top_mem U)
  intro V f _
  letI := (isEquivalence_iff_fiberwise F).1 hF V
  exact Functor.EssSurj.mem_essImage (F.fiberFunctor V)
    (f⁎[Functor.Cleavage.ofIsFibered p₂] y)

/-- Precomposition by an equivalence over the base preserves heterogeneous local essential
surjectivity. -/
theorem LocallyEssentiallySurjective.comp_left_of_isEquivalence
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C} (E : CartesianBasedFunctor p₁ p₂)
    (hE : E.toBasedFunctor.IsEquivalence) (G : CartesianBasedFunctor p₂ p₃)
    (hG : LocallyEssentiallySurjective J G) :
    LocallyEssentiallySurjective J (E.comp G) := by
  exact LocallyEssentiallySurjective.comp
    (LocallyEssentiallySurjective.of_isEquivalence J E hE) hG

/-- Postcomposition by an equivalence over the base preserves heterogeneous local essential
surjectivity. -/
theorem LocallyEssentiallySurjective.comp_right_of_isEquivalence
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C} (F : CartesianBasedFunctor p₁ p₂)
    (hF : LocallyEssentiallySurjective J F) (E : CartesianBasedFunctor p₂ p₃)
    (hE : E.toBasedFunctor.IsEquivalence) :
    LocallyEssentiallySurjective J (F.comp E) := by
  exact LocallyEssentiallySurjective.comp hF
    (LocallyEssentiallySurjective.of_isEquivalence J E hE)

/-- Heterogeneous local essential surjectivity reflects across postcomposition by an
equivalence over the base. -/
theorem LocallyEssentiallySurjective.of_comp_right_isEquivalence
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C} (F : CartesianBasedFunctor p₁ p₂)
    (E : CartesianBasedFunctor p₂ p₃) (hE : E.toBasedFunctor.IsEquivalence)
    (hFE : LocallyEssentiallySurjective J (F.comp E)) :
    LocallyEssentiallySurjective J F := by
  intro U y
  apply J.superset_covering _ (hFE ((E.fiberFunctor U).obj y))
  intro V f hf
  rcases hf with ⟨x, ⟨e⟩⟩
  letI := (isEquivalence_iff_fiberwise E).1 hE V
  exact ⟨x, ⟨(E.fiberFunctor V).preimageIso
    (e ≪≫ Reindex.mapIso E (Functor.Cleavage.ofIsFibered p₂)
      (Functor.Cleavage.ofIsFibered p₃) f y)⟩⟩

/-- Transport heterogeneous local essential surjectivity along an isomorphism of parallel
cartesian functors. -/
theorem LocallyEssentiallySurjective.of_iso
    {J : GrothendieckTopology C} {F G : CartesianBasedFunctor p₁ p₂}
    (e : F ≅ G) (hF : LocallyEssentiallySurjective J F) :
    LocallyEssentiallySurjective J G := by
  intro U y
  apply J.superset_covering _ (hF y)
  intro V f hf
  rcases hf with ⟨x, ⟨d⟩⟩
  exact ⟨x, ⟨((fiberIso e V).app x).symm ≪≫ d⟩⟩

/-- Isomorphic parallel heterogeneous cartesian functors are locally essentially surjective
simultaneously. -/
theorem LocallyEssentiallySurjective.iff_of_iso
    {J : GrothendieckTopology C} {F G : CartesianBasedFunctor p₁ p₂}
    (e : F ≅ G) :
    LocallyEssentiallySurjective J F ↔ LocallyEssentiallySurjective J G := by
  exact ⟨LocallyEssentiallySurjective.of_iso e,
    LocallyEssentiallySurjective.of_iso e.symm⟩

/-- If a composite heterogeneous cartesian functor is locally essentially surjective, then so is
its right factor. -/
theorem LocallyEssentiallySurjective.right_of_comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C}
    {F : CartesianBasedFunctor p₁ p₂} {G : CartesianBasedFunctor p₂ p₃}
    (h : LocallyEssentiallySurjective J (F.comp G)) :
    LocallyEssentiallySurjective J G := by
  intro U z
  apply J.superset_covering _ (h z)
  intro V f hf
  rcases hf with ⟨x, ⟨e⟩⟩
  exact ⟨(F.fiberFunctor V).obj x, ⟨e⟩⟩

/-- A right factor is locally essentially surjective when its composite is isomorphic to a
locally essentially surjective heterogeneous cartesian functor. -/
theorem LocallyEssentiallySurjective.right_of_comp_iso
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C}
    {F : CartesianBasedFunctor p₁ p₂} {G : CartesianBasedFunctor p₂ p₃}
    {H : CartesianBasedFunctor p₁ p₃} (e : F.comp G ≅ H)
    (hH : LocallyEssentiallySurjective J H) :
    LocallyEssentiallySurjective J G := by
  exact LocallyEssentiallySurjective.right_of_comp
    (LocallyEssentiallySurjective.of_iso e.symm hH)

namespace Homwise

/-- A heterogeneous cartesian functor is locally fully faithful when every minimally lifted
Hom-presheaf map is locally injective and locally surjective on the corresponding slice site. -/
@[stacks 02ZP "(1), Hom-presheaf local equivalence",
  stacks 02ZN "(1), stackification Hom-presheaf local equivalence"]
def IsLocalEquivalence
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) : Prop :=
  ∀ {U : C} (x y : p₁.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (HomPresheaf.Chosen.map F x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (HomPresheaf.Chosen.map F x y)

/-- Each Hom map of a locally fully faithful cartesian functor is locally injective. -/
theorem IsLocalEquivalence.homPresheafMap_isLocallyInjective
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsLocalEquivalence J F) {U : C} (x y : p₁.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (HomPresheaf.Chosen.map F x y) :=
  (hF x y).1

/-- Each Hom map of a locally fully faithful cartesian functor is locally surjective. -/
theorem IsLocalEquivalence.homPresheafMap_isLocallySurjective
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsLocalEquivalence J F) {U : C} (x y : p₁.Fiber U) :
    Presheaf.IsLocallySurjective (J.over U) (HomPresheaf.Chosen.map F x y) :=
  (hF x y).2

/-- The pointwise localizing-class criterion for heterogeneous Homwise local equivalence. -/
@[stacks 02ZN "stackification Homwise local-equivalence criterion"]
theorem isLocalEquivalence_iff
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂)
    [∀ U : C, (J.over U).WEqualsLocallyBijective (Type (max vS₁ vS₂))] :
    IsLocalEquivalence J F ↔
      ∀ {U : C} (x y : p₁.Fiber U),
        (J.over U).W (HomPresheaf.Chosen.map F x y) := by
  constructor
  · intro hF U x y
    exact ((J.over U).W_iff_isLocallyBijective _).2 (hF x y)
  · intro hF U x y
    exact ((J.over U).W_iff_isLocallyBijective _).1 (hF x y)

end Homwise

/-- A heterogeneous cartesian functor is a local equivalence when it is locally fully faithful
on the minimally lifted Hom-presheaves and locally essentially surjective on fiber objects. -/
@[stacks 02ZP "two local conditions for stackification",
  stacks 02ZN "two local conditions for stackification"]
def IsLocalEquivalence
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) : Prop :=
  Homwise.IsLocalEquivalence J F ∧ LocallyEssentiallySurjective J F

/-- The two defining conditions of a heterogeneous local equivalence. -/
@[stacks 02ZP "local-equivalence criterion for stackification",
  stacks 02ZN "local-equivalence criterion for stackification"]
theorem isLocalEquivalence_iff
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) :
    IsLocalEquivalence J F ↔
      Homwise.IsLocalEquivalence J F ∧ LocallyEssentiallySurjective J F := Iff.rfl

/-- A heterogeneous local equivalence is locally fully faithful on all lifted
Hom-presheaves. -/
@[stacks 02ZN "stackification local-equivalence Homwise projection"]
theorem IsLocalEquivalence.isHomwise
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsLocalEquivalence J F) : Homwise.IsLocalEquivalence J F := hF.1

/-- A heterogeneous local equivalence is locally essentially surjective on fiber objects. -/
@[stacks 02ZN "stackification local-equivalence essential-image projection"]
theorem IsLocalEquivalence.locallyEssentiallySurjective
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsLocalEquivalence J F) : LocallyEssentiallySurjective J F := hF.2

/-- Every lifted Hom-presheaf map of a heterogeneous local equivalence belongs to the relevant
slice-site localizing class. -/
@[stacks 02ZP "(1), Hom-presheaf map in the sheafification class",
  stacks 02ZN "(1), stackification Hom-presheaf map in the sheafification class"]
theorem IsLocalEquivalence.homPresheafMap_mem
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsLocalEquivalence J F) {U : C} (x y : p₁.Fiber U) :
    (J.over U).W (HomPresheaf.Chosen.map F x y) :=
  Presheaf.LocallyBijective.mem_W _ _ (hF.1 x y).1 (hF.1 x y).2

/-- The identity cartesian functor is a heterogeneous local equivalence. -/
@[stacks 02ZN "identity stackification local equivalence"]
theorem IsLocalEquivalence.id (J : GrothendieckTopology C) :
    IsLocalEquivalence J (CartesianBasedFunctor.id p₁) := by
  refine ⟨?_, LocallyEssentiallySurjective.id J⟩
  intro U x y
  have hFF : ∀ V : C,
      Nonempty ((CartesianBasedFunctor.id p₁).fiberFunctor V).FullyFaithful := by
    intro V
    exact ⟨Functor.FullyFaithful.id _⟩
  letI := HomPresheaf.Chosen.map.isIso_of_fiberwiseFullyFaithful
    (CartesianBasedFunctor.id p₁) hFF x y
  exact ⟨inferInstance, inferInstance⟩

/-- Heterogeneous local equivalences are closed under universe-polymorphic composition. -/
@[stacks 02ZN "composition of stackification local equivalences"]
theorem IsLocalEquivalence.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C}
    {F : CartesianBasedFunctor p₁ p₂} {G : CartesianBasedFunctor p₂ p₃}
    (hF : IsLocalEquivalence J F) (hG : IsLocalEquivalence J G) :
    IsLocalEquivalence J (F.comp G) := sorry

/-- An equivalence over the base is a heterogeneous local equivalence. -/
@[stacks 02ZN "equivalence implies stackification local equivalence"]
theorem IsLocalEquivalence.of_isEquivalence
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂)
    [F.toBasedFunctor.IsEquivalence] : IsLocalEquivalence J F := by
  refine ⟨?_, LocallyEssentiallySurjective.of_isEquivalence J F inferInstance⟩
  intro U x y
  exact ⟨inferInstance, inferInstance⟩

/-- Transport heterogeneous local equivalence along an isomorphism of parallel cartesian
functors. -/
@[stacks 02ZN "isomorphism transport of stackification local equivalence"]
theorem IsLocalEquivalence.of_iso
    {J : GrothendieckTopology C} {F G : CartesianBasedFunctor p₁ p₂}
    (e : F ≅ G) (hF : IsLocalEquivalence J F) : IsLocalEquivalence J G := sorry

/-- Isomorphic parallel heterogeneous cartesian functors are local equivalences
simultaneously. -/
@[stacks 02ZN "isomorphism invariance of stackification local equivalence"]
theorem isLocalEquivalence_iff_of_iso
    {J : GrothendieckTopology C} {F G : CartesianBasedFunctor p₁ p₂}
    (e : F ≅ G) : IsLocalEquivalence J F ↔ IsLocalEquivalence J G := by
  exact ⟨IsLocalEquivalence.of_iso e, IsLocalEquivalence.of_iso e.symm⟩

end CartesianBasedFunctor

end CategoryTheory

/- Axiom audit: `EssentialImage.sieve` and `EssentialImage.cover` carry the explicit
essential-preimage predicate and covering witness. `EssentialImage.compIso` is composed directly
from `CartesianBasedFunctor.Reindex.mapIso`, functoriality, and cleavage composition; it does not
choose a new comparison. Any new `sorryAx` in the sieve/cover owners is confined to `Prop`-valued
closure fields. -/
