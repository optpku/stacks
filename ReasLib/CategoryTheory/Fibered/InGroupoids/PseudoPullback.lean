/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Groupoid
import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids
import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Computations
import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Involution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Based pseudo-pullbacks of groupoid fibrations

Closure of `Functor.IsFibered.InGroupoids` under the explicit based pseudo-pullback model and
its two projections. The statements concern raw projections and based functors, without choosing
the full subbicategory of groupoid-fibred categories.
-/

@[expose] public section

universe u v uX vX uY vY uS vS

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty Functor IsHomLift
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.PseudoPullback

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

set_option backward.isDefEq.respectTransparency false in
/-- Transport strong cartesianness to the displayed base arrow of a lift. -/
private theorem stronglyCartesianAt
    {A : Type*} [Category A] (p : A ⥤ C) {a b : A} (φ : a ⟶ b)
    (h : p.IsStronglyCartesian (p.map φ) φ) {U V : C} (f : U ⟶ V)
    (hf : p.IsHomLift f φ) : p.IsStronglyCartesian f φ := by
  cases hf
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Recover the common base arrow from the first component and its endpoint identifications. -/
private theorem baseMapViaFst
    {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S} {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    baseMap φ = (fstBaseIso P).inv ≫ X.p.map (fstMap φ) ≫ (fstBaseIso Q).hom := by
  rw [fstBaseIso.naturality φ, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A strongly cartesian second component makes the first projection strongly cartesian.
The factor is the original second-component Cartesian factor, paired with the given first map. -/
private theorem fstStronglyCartesian
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (hG : G.PreservesStronglyCartesian)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q)
    (hφ : Y.p.IsStronglyCartesian (baseMap φ) (sndMap φ)) :
    (fst F G).toFunctor.IsStronglyCartesian (fstMap φ) φ := by
  letI := hφ
  letI : S.p.IsStronglyCartesian (baseMap φ) (G.toFunctor.map (sndMap φ)) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift (⟨G, hG⟩ : CartesianBasedFunctor Y.p S.p) _ _ hφ
  letI : (fst F G).toFunctor.IsHomLift (fstMap φ) φ := by
    simpa only [fst.map] using (IsHomLift.map (fst F G).toFunctor φ)
  constructor
  intro R α ψ hψ
  letI := hψ
  have hfst : fstMap ψ = α ≫ fstMap φ :=
    (IsHomLift.eq_of_isHomLift (fst F G).toFunctor _ ψ).symm
  let k : baseObj R ⟶ baseObj P :=
    (fstBaseIso R).inv ≫ X.p.map α ≫ (fstBaseIso P).hom
  letI : X.p.IsHomLift k α :=
    IsHomLift.of_fac X.p k α (fiberObj R).fst.2 (fiberObj P).fst.2 rfl
  have hb : baseMap ψ = k ≫ baseMap φ := by
    rw [baseMapViaFst ψ, hfst, X.p.map_comp, baseMapViaFst φ]
    dsimp [k, fstBaseIso]
    simp
  let δ := IsStronglyCartesian.map Y.p (baseMap φ) (sndMap φ) hb (sndMap ψ)
  letI : Y.p.IsHomLift k δ :=
    IsStronglyCartesian.map_isHomLift Y.p _ _ hb _
  letI : S.p.IsHomLift k (F.toFunctor.map α) :=
    BasedFunctor.preserves_isHomLift F k α
  letI : S.p.IsHomLift k (G.toFunctor.map δ) :=
    BasedFunctor.preserves_isHomLift G k δ
  have hw : CommSq (F.toFunctor.map α) (comparison R) (comparison P)
      (G.toFunctor.map δ) := by
    constructor
    apply IsStronglyCartesian.ext S.p (baseMap φ) (G.toFunctor.map (sndMap φ)) k
    calc
      (F.toFunctor.map α ≫ comparison P) ≫ G.toFunctor.map (sndMap φ) =
          F.toFunctor.map (α ≫ fstMap φ) ≫ comparison Q := by
            simp only [F.toFunctor.map_comp, Category.assoc, (comm φ).w]
      _ = F.toFunctor.map (fstMap ψ) ≫ comparison Q := by rw [hfst]
      _ = comparison R ≫ G.toFunctor.map (sndMap ψ) := (comm ψ).w
      _ = (comparison R ≫ G.toFunctor.map δ) ≫ G.toFunctor.map (sndMap φ) := by
        rw [Category.assoc, ← G.toFunctor.map_comp, IsStronglyCartesian.fac]
  let χ := Hom.mk k α inferInstance δ inferInstance hw
  refine ⟨χ, ⟨.map χ, ?_⟩, ?_⟩
  · apply hom_ext
    · exact hfst.symm
    · exact IsStronglyCartesian.fac Y.p _ _ hb _
  · rintro χ' ⟨hχ', hfac⟩
    letI := hχ'
    have hχfst : fstMap χ' = α :=
      (IsHomLift.eq_of_isHomLift (fst F G).toFunctor α χ').symm
    have hχbase : baseMap χ' = k := by
      rw [baseMapViaFst χ', hχfst]
    letI : Y.p.IsHomLift k (sndMap χ') := hχbase ▸ sndMap.isHomLift χ'
    apply hom_ext
    · exact hχfst
    · apply IsStronglyCartesian.map_uniq Y.p (baseMap φ) (sndMap φ) hb (sndMap ψ)
      simpa only [sndMap.comp] using congrArg sndMap hfac

set_option backward.isDefEq.respectTransparency false in
/-- Lift through the original second fibration and compare the two Cartesian arrows in the target.
The lifted first component is exactly the specified source object. -/
private theorem fstFibered
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (hG : G.PreservesStronglyCartesian) [Y.p.IsFibered]
    (hF : ∀ {a b : X.obj} (α : a ⟶ b),
      S.p.IsStronglyCartesian (S.p.map (F.toFunctor.map α)) (F.toFunctor.map α)) :
    (fst F G).toFunctor.IsFibered := by
  apply IsFibered.of_exists_isStronglyCartesian
  intro P x α
  let f : X.p.obj x ⟶ baseObj P := X.p.map α ≫ (fstBaseIso P).hom
  letI : X.p.IsHomLift (X.p.map α) α := .map α
  letI : X.p.IsHomLift f α :=
    IsHomLift.lift_comp_eqToHom X.p (X.p.map α) α (fiberObj P).fst.2
  obtain ⟨y, β, hβ⟩ := IsPreFibered.exists_isCartesian Y.p (fiberObj P).snd.2 f
  letI := hβ
  letI : Y.p.IsHomLift f β := hβ.toIsHomLift
  letI : S.p.IsHomLift f (F.toFunctor.map α) :=
    BasedFunctor.preserves_isHomLift F f α
  letI : S.p.IsStronglyCartesian f (F.toFunctor.map α) :=
    stronglyCartesianAt S.p _ (hF α) f inferInstance
  letI : S.p.IsStronglyCartesian f (G.toFunctor.map β) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift (⟨G, hG⟩ : CartesianBasedFunctor Y.p S.p) f β inferInstance
  letI : S.p.IsCartesian f (F.toFunctor.map α) :=
    IsStronglyCartesian.isCartesian_of_isStronglyCartesian S.p f (F.toFunctor.map α)
  letI : S.p.IsCartesian f (G.toFunctor.map β) :=
    IsStronglyCartesian.isCartesian_of_isStronglyCartesian S.p f (G.toFunctor.map β)
  letI : S.p.IsHomLift (𝟙 (baseObj P)) (comparisonIsoApp P).hom :=
    comparisonIsoApp.hom.isHomLift P
  letI : S.p.IsCartesian f (F.toFunctor.map α ≫ (comparisonIsoApp P).hom) :=
    IsCartesian.of_comp_iso S.p f _ (comparisonIsoApp P)
  let i := IsCartesian.domainUniqueUpToIso S.p f (G.toFunctor.map β)
    (F.toFunctor.map α ≫ (comparisonIsoApp P).hom)
  let j : (F.fiberFunctor (X.p.obj x)).obj ⟨x, rfl⟩ ≅
      (G.fiberFunctor (X.p.obj x)).obj ⟨y, IsHomLift.domain_eq Y.p f β⟩ :=
    { hom := ⟨i.hom, inferInstance⟩
      inv := ⟨i.inv, inferInstance⟩
      hom_inv_id := Subtype.ext i.hom_inv_id
      inv_hom_id := Subtype.ext i.inv_hom_id }
  let R := mk F G (X.p.obj x)
    { fst := ⟨x, rfl⟩
      snd := ⟨y, IsHomLift.domain_eq Y.p f β⟩
      iso := j }
  have hw : CommSq (F.toFunctor.map α) (comparison R) (comparison P)
      (G.toFunctor.map β) := by
    constructor
    exact (IsCartesian.fac S.p f (G.toFunctor.map β)
      (F.toFunctor.map α ≫ (comparisonIsoApp P).hom)).symm
  let φ : R ⟶ P := Hom.mk f α inferInstance β inferInstance hw
  refine ⟨R, φ, ?_⟩
  exact fstStronglyCartesian F G hG φ
    (IsFibered.isStronglyCartesian_of_isCartesian Y.p f β)

set_option backward.isDefEq.respectTransparency false in
/-- When the second source is fibred in groupoids, every first-projection arrow is Cartesian. -/
private theorem fstInGroupoids
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (hG : G.PreservesStronglyCartesian)
    [IsFibered.InGroupoids Y.p]
    (hF : ∀ {a b : X.obj} (α : a ⟶ b),
      S.p.IsStronglyCartesian (S.p.map (F.toFunctor.map α)) (F.toFunctor.map α)) :
    IsFibered.InGroupoids (fst F G).toFunctor where
  toIsFibered := fstFibered F G hG hF
  all_isCartesian φ := by
    letI : Y.p.IsStronglyCartesian (baseMap φ) (sndMap φ) :=
      stronglyCartesianAt Y.p _
        (IsFibered.isStronglyCartesian_of_isCartesian Y.p _ (sndMap φ))
        (baseMap φ) (sndMap.isHomLift φ)
    letI := fstStronglyCartesian F G hG φ inferInstance
    exact IsStronglyCartesian.isCartesian_of_isStronglyCartesian (fst F G).toFunctor
      (fstMap φ) φ

set_option backward.isDefEq.respectTransparency false in
/-- Transport the first-projection properties along the explicit involutive swap over the
second source. Both directions of the equivalence are the existing swap functors. -/
private theorem sndClosureBySwap (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    ((fst G F).toFunctor.IsFibered → (snd F G).toFunctor.IsFibered) ∧
      (IsFibered.InGroupoids (fst G F).toFunctor →
        IsFibered.InGroupoids (snd F G).toFunctor) := by
  let s : ofFunctor (snd F G).toFunctor ⥤ᵇ ofFunctor (fst G F).toFunctor :=
    { toFunctor := (swap F G).toFunctor
      w := congrArg BasedFunctor.toFunctor (swap.fst F G) }
  let t : ofFunctor (fst G F).toFunctor ⥤ᵇ ofFunctor (snd F G).toFunctor :=
    { toFunctor := (swap G F).toFunctor
      w := congrArg BasedFunctor.toFunctor (swap.snd G F) }
  have hs : s ⋙ t = 𝟭 (ofFunctor (snd F G).toFunctor) := by
    apply BasedFunctor.ext
    exact congrArg (fun K : PseudoPullback F G ⥤ᵇ PseudoPullback F G ↦ K.toFunctor)
      (swap.involution.eqId F G)
  have ht : t ⋙ s = 𝟭 (ofFunctor (fst G F).toFunctor) := by
    apply BasedFunctor.ext
    exact congrArg (fun K : PseudoPullback G F ⥤ᵇ PseudoPullback G F ↦ K.toFunctor)
      (swap.involution.eqId G F)
  letI : s.IsEquivalence :=
    ⟨⟨{ inverse := t, unitIso := eqToIso hs.symm, counitIso := eqToIso ht }⟩⟩
  exact ⟨(BasedFunctor.IsEquivalence.isFibered_iff s).mpr,
    (BasedFunctor.IsEquivalence.inGroupoids_iff s).mpr⟩

set_option backward.isDefEq.respectTransparency false in
/-- The first projection from a pseudo-pullback of cartesian functors is fibred when its base
source is fibred in groupoids and the opposite source is fibred. No groupoid condition is needed
on the fibers of the opposite source or the common target. -/
instance Fst.IsFibered.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InGroupoids X.p] [Y.p.IsFibered] :
    (PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor).toFunctor.IsFibered :=
  fstFibered (X := X) (Y := Y) (S := S)
    F.toBasedFunctor G.toBasedFunctor G.preservesStronglyCartesian
    (fun α ↦ F.preservesStronglyCartesian α
      (IsFibered.isStronglyCartesian_of_isCartesian X.p (X.p.map α) α))

set_option backward.isDefEq.respectTransparency false in
/-- The second projection from a pseudo-pullback of cartesian functors is fibred when its base
source is fibred in groupoids and the opposite source is fibred. This is the symmetric companion
to `Fst.IsFibered.ofCartesian`. -/
instance Snd.IsFibered.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] :
    (PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor).toFunctor.IsFibered :=
  (sndClosureBySwap F.toBasedFunctor G.toBasedFunctor).1
    (fstFibered (X := Y) (Y := X) (S := S)
      G.toBasedFunctor F.toBasedFunctor F.preservesStronglyCartesian
      (fun α ↦ G.preservesStronglyCartesian α
        (IsFibered.isStronglyCartesian_of_isCartesian Y.p (Y.p.map α) α)))

set_option backward.isDefEq.respectTransparency false in
/-- Every standard fibre of the explicit based pseudo-pullback projection is a groupoid. -/
instance Fiber.isGroupoid (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (U : C)
    [IsGroupoid (X.p.Fiber U)] [IsGroupoid (Y.p.Fiber U)] :
    IsGroupoid ((BasedCategory.PseudoPullback F G).p.Fiber U) := by
  constructor
  intro P Q φ
  let L := Fiber.comparison F G U
  let R := Fiber.comparisonInverse F G U
  letI : IsIso (L.map φ) :=
    (Limits.CategoricalPullback.isIso_iff (F.fiberFunctor U) (G.fiberFunctor U) _).mpr
      ⟨IsGroupoid.all_isIso (C := X.p.Fiber U) (L.map φ).fst,
        IsGroupoid.all_isIso (C := Y.p.Fiber U) (L.map φ).snd⟩
  let e := Fiber.comparison.unitIso F G U
  have hφ : φ = e.hom.app P ≫ R.map (L.map φ) ≫ e.inv.app Q := by
    calc
      φ = (φ ≫ e.hom.app Q) ≫ e.inv.app Q := by simp
      _ = (e.hom.app P ≫ R.map (L.map φ)) ≫ e.inv.app Q :=
        congrArg (· ≫ e.inv.app Q) (e.hom.naturality φ)
      _ = _ := Category.assoc _ _ _
  rw [hφ]
  infer_instance

/- The inverse functor and unit are explicit; invertibility is transported without selecting
quasi-inverse data from the deferred `Fiber.comparison.isEquivalence` instance. -/

/-- The pseudo-pullback of two cartesian based functors with groupoid-fibred domains is again
fibred in groupoids. The common target need not itself be fibred in groupoids: its only role in
the fibredness argument is through preservation of strongly cartesian arrows by the two legs. -/
instance Projection.InGroupoids.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] :
    Functor.IsFibered.InGroupoids
      (BasedCategory.PseudoPullback F.toBasedFunctor G.toBasedFunctor).p :=
  Functor.IsFibered.InGroupoids.of_isFibered_fibersGroupoid _
    (projectionIsFibered (X := X) (Y := Y) (S := S) F G)
    (fun U ↦ Fiber.isGroupoid (X := X) (Y := Y) (S := S)
      F.toBasedFunctor G.toBasedFunctor U)
/- Proof strategy: use `BasedCategory.PseudoPullback.projectionIsFibered F G` for fibredness and
`Fiber.isGroupoid F.toBasedFunctor G.toBasedFunctor` on each standard fibre. -/

/-- The projection of a based pseudo-pullback of categories fibred
in groupoids is again fibred in groupoids. This is the convenient unbundled specialization of
`Projection.InGroupoids.ofCartesian`: every based functor into the groupoid-fibred common target
preserves strongly cartesian arrows. -/
@[stacks 0041 "(1)"]
instance Projection.inGroupoids (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
    [Functor.IsFibered.InGroupoids S.p] :
    Functor.IsFibered.InGroupoids (BasedCategory.PseudoPullback F G).p := by
  let cF : CartesianBasedFunctor X.p S.p :=
    ⟨F, fun {_ _} α _ ↦
      IsFibered.isStronglyCartesian_of_isCartesian S.p (S.p.map (F.map α)) (F.map α)⟩
  let cG : CartesianBasedFunctor Y.p S.p :=
    ⟨G, fun {_ _} α _ ↦
      IsFibered.isStronglyCartesian_of_isCartesian S.p (S.p.map (G.map α)) (G.map α)⟩
  exact Projection.InGroupoids.ofCartesian (X := X) (Y := Y) (S := S) cF cG
/- The preservation certificates use the original target's Cartesian field, upgraded by
mathlib's fibredness theorem. The bundled functors retain exactly `F` and `G`. -/

set_option backward.isDefEq.respectTransparency false in
/-- The first projection from the pseudo-pullback of cartesian morphisms between
groupoid-fibred sources is fibred in groupoids. The common target need not itself be fibred in
groupoids. -/
instance Fst.InGroupoids.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] :
    Functor.IsFibered.InGroupoids
      (PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor).toFunctor :=
  fstInGroupoids (X := X) (Y := Y) (S := S)
    F.toBasedFunctor G.toBasedFunctor G.preservesStronglyCartesian
    (fun α ↦ F.preservesStronglyCartesian α
      (IsFibered.isStronglyCartesian_of_isCartesian X.p (X.p.map α) α))
/- Proof strategy: lift an arrow through `Y.p`. Both its image under `G` and the image under `F`
of the given arrow of `X` are strongly cartesian, so uniqueness supplies the vertical comparison
isomorphism. The groupoid fibres of `Y.p` identify the fibres of `fst` as groupoids. -/

set_option backward.isDefEq.respectTransparency false in
/-- The second projection from the pseudo-pullback of cartesian morphisms between
groupoid-fibred sources is fibred in groupoids. The common target need not itself be fibred in
groupoids. -/
instance Snd.InGroupoids.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] :
    Functor.IsFibered.InGroupoids
      (PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor).toFunctor :=
  (sndClosureBySwap F.toBasedFunctor G.toBasedFunctor).2
    (Fst.InGroupoids.ofCartesian (X := Y) (Y := X) (S := S) G F)
/- Proof strategy: use the symmetric construction, lifting through `X.p`; the groupoid fibres of
`X.p` give the fibres of `snd`. -/

set_option backward.isDefEq.respectTransparency false in
/-- The first projection from a based pseudo-pullback is fibred in groupoids whenever the
opposite source and the common target are fibred in groupoids. No condition on the projected
source is needed. This is the general base-change API behind the slice specialization in
`PseudoPullback.fstGroupoids`. -/
instance Fst.inGroupoids
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [Functor.IsFibered.InGroupoids Y.p]
    [Functor.IsFibered.InGroupoids S.p] :
    Functor.IsFibered.InGroupoids (PseudoPullback.fst F G).toFunctor :=
  fstInGroupoids F G
    (fun {_ _} α _ ↦ IsFibered.isStronglyCartesian_of_isCartesian S.p _ (G.toFunctor.map α))
    (fun α ↦ IsFibered.isStronglyCartesian_of_isCartesian S.p _ (F.toFunctor.map α))
/- Proof strategy: lift an arrow of `X` through `Y.p`. Every arrow of `S` is strongly cartesian,
so strong-cartesian uniqueness supplies the vertical comparison isomorphism needed for an object
and arrow of the pseudo-pullback. The groupoid fibres of `Y.p` give groupoid fibres of `fst`. -/

set_option backward.isDefEq.respectTransparency false in
/-- The second projection from a based pseudo-pullback is fibred in groupoids whenever the
opposite source and the common target are fibred in groupoids. No condition on the projected
source is needed. -/
instance Snd.inGroupoids
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids S.p] :
    Functor.IsFibered.InGroupoids (PseudoPullback.snd F G).toFunctor :=
  (sndClosureBySwap F G).2 (Fst.inGroupoids G F)
/- Proof strategy: symmetrically lift an arrow of `Y` through `X.p`, use strong-cartesian
uniqueness in `S` to transport the comparison isomorphism, and use the groupoid fibres of `X.p`
for the fibres of `snd`. -/

end BasedCategory.PseudoPullback

end CategoryTheory
