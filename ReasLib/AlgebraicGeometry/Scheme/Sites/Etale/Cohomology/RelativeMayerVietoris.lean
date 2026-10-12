/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.MayerVietoris
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace EtaleRelativeMayerVietoris

variable {X Y : Scheme.{u}}

/-- Restrict an abelian sheaf to an open `W ⊆ X` and then take its small-etale
direct image along `W ⟶ X ⟶ Y`. This is `a_*(-|_W)` when `W = U`, and likewise
for `b_*` and `c_*`. -/
noncomputable abbrev along (f : X ⟶ Y) (W : X.Opens) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  Scheme.etaleRestrictionSheaf W.ι AddCommGrpCat.{u} ⋙
    (Scheme.smallEtalePullback (W.ι ≫ f)).sheafPushforwardContinuous
      AddCommGrpCat.{u} Y.smallEtaleTopology W.toScheme.smallEtaleTopology

/-- Composition of small-etale pullback along `W ⟶ Y` with étale restriction to `X`
is continuous. -/
instance siteToAlong_isContinuous (f : X ⟶ Y) (W : X.Opens) :
    (Scheme.smallEtalePullback (W.ι ≫ f) ⋙ Scheme.etaleRestriction W.ι).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := sorry

/-- The site-level comparison
`smallEtalePullback (W.ι ≫ f) ⋙ etaleRestriction W.ι ⟶ smallEtalePullback f`. -/
noncomputable def siteToAlong (f : X ⟶ Y) (W : X.Opens) :
    Scheme.smallEtalePullback (W.ι ≫ f) ⋙ Scheme.etaleRestriction W.ι ⟶
      Scheme.smallEtalePullback f :=
  MorphismProperty.Over.pullbackMapHomPullback
    (P := @Etale) (Q := (⊤ : MorphismProperty Scheme))
    W.ι (inferInstance : Etale W.ι) (MorphismProperty.top_apply W.ι) f

/-- Underived comparison `f_* ⟶ a_*(-|_W)` from the site-level pullback comparison. -/
noncomputable def toAlong (f : X ⟶ Y) (W : X.Opens) :
    (Scheme.smallEtalePullback f).sheafPushforwardContinuous
      AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology ⟶
      along f W :=
  Functor.sheafPushforwardContinuousNatTrans (siteToAlong f W)
      AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology ≫
    (Functor.sheafPushforwardContinuousComp
      (Scheme.smallEtalePullback (W.ι ≫ f)) (Scheme.etaleRestriction W.ι)
      AddCommGrpCat.{u} Y.smallEtaleTopology W.toScheme.smallEtaleTopology
      X.smallEtaleTopology).inv

/-- Site-level comparison from the intersection open to the first open, after
base change along `f`. -/
noncomputable def siteToIntersectionLeft (f : X ⟶ Y) (U V : X.Opens) :
    Scheme.smallEtalePullback ((U ⊓ V).ι ≫ f) ⋙ Scheme.etaleRestriction (U ⊓ V).ι ⟶
      Scheme.smallEtalePullback (U.ι ≫ f) ⋙ Scheme.etaleRestriction U.ι where
  app A :=
    MorphismProperty.Over.homMk
      (pullback.map A.hom ((U ⊓ V).ι ≫ f) A.hom (U.ι ≫ f)
        (𝟙 A.left) (X.homOfLE inf_le_left) (𝟙 Y)
        sorry sorry)
      sorry sorry
  naturality := sorry

/-- Site-level comparison from the intersection open to the second open, after
base change along `f`. -/
noncomputable def siteToIntersectionRight (f : X ⟶ Y) (U V : X.Opens) :
    Scheme.smallEtalePullback ((U ⊓ V).ι ≫ f) ⋙ Scheme.etaleRestriction (U ⊓ V).ι ⟶
      Scheme.smallEtalePullback (V.ι ≫ f) ⋙ Scheme.etaleRestriction V.ι where
  app A :=
    MorphismProperty.Over.homMk
      (pullback.map A.hom ((U ⊓ V).ι ≫ f) A.hom (V.ι ≫ f)
        (𝟙 A.left) (X.homOfLE inf_le_right) (𝟙 Y)
        sorry sorry)
      sorry sorry
  naturality := sorry

/-- Underived restriction `a_*(-|_U) ⟶ c_*(-|_{U ∩ V})`. -/
noncomputable def toIntersectionLeft (f : X ⟶ Y) (U V : X.Opens) :
    along f U ⟶ along f (U ⊓ V) :=
  (Functor.sheafPushforwardContinuousComp
      (Scheme.smallEtalePullback (U.ι ≫ f)) (Scheme.etaleRestriction U.ι)
      AddCommGrpCat.{u} Y.smallEtaleTopology U.toScheme.smallEtaleTopology
      X.smallEtaleTopology).hom ≫
    Functor.sheafPushforwardContinuousNatTrans (siteToIntersectionLeft f U V)
      AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology ≫
    (Functor.sheafPushforwardContinuousComp
      (Scheme.smallEtalePullback ((U ⊓ V).ι ≫ f)) (Scheme.etaleRestriction (U ⊓ V).ι)
      AddCommGrpCat.{u} Y.smallEtaleTopology (U ⊓ V).toScheme.smallEtaleTopology
      X.smallEtaleTopology).inv

/-- Underived restriction `b_*(-|_V) ⟶ c_*(-|_{U ∩ V})`. -/
noncomputable def toIntersectionRight (f : X ⟶ Y) (U V : X.Opens) :
    along f V ⟶ along f (U ⊓ V) :=
  (Functor.sheafPushforwardContinuousComp
      (Scheme.smallEtalePullback (V.ι ≫ f)) (Scheme.etaleRestriction V.ι)
      AddCommGrpCat.{u} Y.smallEtaleTopology V.toScheme.smallEtaleTopology
      X.smallEtaleTopology).hom ≫
    Functor.sheafPushforwardContinuousNatTrans (siteToIntersectionRight f U V)
      AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology ≫
    (Functor.sheafPushforwardContinuousComp
      (Scheme.smallEtalePullback ((U ⊓ V).ι ≫ f)) (Scheme.etaleRestriction (U ⊓ V).ι)
      AddCommGrpCat.{u} Y.smallEtaleTopology (U ⊓ V).toScheme.smallEtaleTopology
      X.smallEtaleTopology).inv

/-- The small-etale site object over `X` obtained by pulling `W ⟶ Y` back along
an étale morphism `T ⟶ Y`. -/
noncomputable abbrev pulledSite (f : X ⟶ Y) (W : X.Opens) : Y.Etale ⥤ X.Etale :=
  Scheme.smallEtalePullback (W.ι ≫ f) ⋙ Scheme.etaleRestriction W.ι

/-- The commutative square in `Xₑₜ` obtained by pulling `U`, `V`, and `U ∩ V`
back along an étale morphism `T ⟶ Y`. -/
noncomputable def pulledOpenSquare (f : X ⟶ Y) (U V : X.Opens) (T : Y.Etale) :
    Square X.Etale where
  X₁ := (pulledSite f (U ⊓ V)).obj T
  X₂ := (pulledSite f U).obj T
  X₃ := (pulledSite f V).obj T
  X₄ := (Scheme.smallEtalePullback f).obj T
  f₁₂ := (siteToIntersectionLeft f U V).app T
  f₁₃ := (siteToIntersectionRight f U V).app T
  f₂₄ := (siteToAlong f U).app T
  f₃₄ := (siteToAlong f V).app T
  fac := sorry

/-- The first pulled open-to-space arrow is a monomorphism. -/
instance pulledOpenSquare_mono_f₂₄ (f : X ⟶ Y) (U V : X.Opens) (T : Y.Etale) :
    Mono (pulledOpenSquare f U V T).f₂₄ := sorry

/-- The second pulled open-to-space arrow is a monomorphism. -/
instance pulledOpenSquare_mono_f₃₄ (f : X ⟶ Y) (U V : X.Opens) (T : Y.Etale) :
    Mono (pulledOpenSquare f U V T).f₃₄ := sorry

/-- The pulled open-intersection square is a pullback in `Xₑₜ`. -/
theorem pulledOpenSquare_isPullback (f : X ⟶ Y) (U V : X.Opens) (T : Y.Etale) :
    (pulledOpenSquare f U V T).IsPullback := sorry

/-- If `U` and `V` cover `X`, the pulled maps cover the pulled ambient object. -/
theorem pulledOpenSquare_mem_smallEtaleTopology (f : X ⟶ Y) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (T : Y.Etale) :
    Sieve.ofTwoArrows (pulledOpenSquare f U V T).f₂₄ (pulledOpenSquare f U V T).f₃₄ ∈
      X.smallEtaleTopology (pulledOpenSquare f U V T).X₄ := sorry

/-- The Mayer--Vietoris square of the open cover after base change along `T ⟶ Y`. -/
noncomputable def pulledCoverSquare (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (T : Y.Etale)
    [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    X.smallEtaleTopology.MayerVietorisSquare :=
  .mk_of_isPullback (pulledOpenSquare f U V T) (pulledOpenSquare_isPullback f U V T)
    (pulledOpenSquare_mem_smallEtaleTopology f U V hUV T)

/-- Sheafification of `T ↦ H^n((W_T)ₑₜ, F)`, the cohomology description of
`R^n` of restriction to `W` followed by small-etale direct image to `Y`. -/
noncomputable def higherAlong (f : X ⟶ Y) (W : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj F :=
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      ((pulledSite f W).op ⋙ F.cohomologyPresheaf n)
  map {F G} φ :=
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
      (Functor.whiskerLeft (pulledSite f W).op
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map φ))
  map_id := sorry
  map_comp := sorry

/-- Sheafification of `T ↦ H^n((X_T)ₑₜ, F)`, the cohomology description of
`R^n f_*` on `Yₑₜ`. -/
noncomputable def relativeHigherDirectImage (f : X ⟶ Y) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj F :=
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      ((Scheme.smallEtalePullback f).op ⋙ F.cohomologyPresheaf n)
  map {F G} φ :=
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
      (Functor.whiskerLeft (Scheme.smallEtalePullback f).op
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map φ))
  map_id := sorry
  map_comp := sorry

/-- Restriction of cohomology along `X_T ⟶ W_T`. -/
noncomputable def toAlongCohomology (f : X ⟶ Y) (W : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (Scheme.smallEtalePullback f).op ⋙ F.cohomologyPresheaf n ⟶
      (pulledSite f W).op ⋙ F.cohomologyPresheaf n where
  app T := (F.cohomologyPresheaf n).map ((siteToAlong f W).app T.unop).op
  naturality := sorry

/-- Restriction of cohomology along `U_T ⟶ (U ∩ V)_T`. -/
noncomputable def toIntersectionCohomologyLeft (f : X ⟶ Y) (U V : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (pulledSite f U).op ⋙ F.cohomologyPresheaf n ⟶
      (pulledSite f (U ⊓ V)).op ⋙ F.cohomologyPresheaf n where
  app T := (F.cohomologyPresheaf n).map ((siteToIntersectionLeft f U V).app T.unop).op
  naturality := sorry

/-- Restriction of cohomology along `V_T ⟶ (U ∩ V)_T`. -/
noncomputable def toIntersectionCohomologyRight (f : X ⟶ Y) (U V : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (pulledSite f V).op ⋙ F.cohomologyPresheaf n ⟶
      (pulledSite f (U ⊓ V)).op ⋙ F.cohomologyPresheaf n where
  app T := (F.cohomologyPresheaf n).map ((siteToIntersectionRight f U V).app T.unop).op
  naturality := sorry

/-- Pointwise biproduct of the two open higher-direct-image functors. -/
noncomputable def higherAlongBiprod (f : X ⟶ Y) (U V : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj F := (higherAlong f U n).obj F ⊞ (higherAlong f V n).obj F
  map {F G} φ := biprod.map ((higherAlong f U n).map φ) ((higherAlong f V n).map φ)
  map_id := sorry
  map_comp := sorry

/-- Restriction pair `R^n f_* ⟶ R^n a_*(-|_U) ⊞ R^n b_*(-|_V)`, as the
sheafification of the Mayer--Vietoris restriction pair on pullbacks. -/
noncomputable def toOpens (f : X ⟶ Y) (U V : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    relativeHigherDirectImage f n ⟶ higherAlongBiprod f U V n where
  app F :=
    biprod.lift
      ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
        (toAlongCohomology f U n F))
      ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
        (toAlongCohomology f V n F))
  naturality := sorry

/-- Component of the restriction pair on a coefficient sheaf. -/
theorem toOpens_app (f : X ⟶ Y) (U V : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toOpens f U V n).app F =
      biprod.lift
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
          (toAlongCohomology f U n F))
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
          (toAlongCohomology f V n F)) := sorry

/-- Difference of restrictions
`R^n a_*(-|_U) ⊞ R^n b_*(-|_V) ⟶ R^n c_*(-|_{U ∩ V})`. -/
noncomputable def toIntersection (f : X ⟶ Y) (U V : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    higherAlongBiprod f U V n ⟶ higherAlong f (U ⊓ V) n where
  app F :=
    biprod.desc
      ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
        (toIntersectionCohomologyLeft f U V n F))
      (-(presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
        (toIntersectionCohomologyRight f U V n F))
  naturality := sorry

/-- Component of the difference map on a coefficient sheaf. -/
theorem toIntersection_app (f : X ⟶ Y) (U V : X.Opens) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toIntersection f U V n).app F =
      biprod.desc
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
          (toIntersectionCohomologyLeft f U V n F))
        (-(presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
          (toIntersectionCohomologyRight f U V n F)) := sorry

/-- Connecting homomorphism of the pulled Mayer--Vietoris square, as a
presheaf map `T ↦ H^n((U ∩ V)_T, F) ⟶ H^{n+1}(X_T, F)`. -/
noncomputable def boundaryPresheaf (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (pulledSite f (U ⊓ V)).op ⋙ F.cohomologyPresheaf n ⟶
      (Scheme.smallEtalePullback f).op ⋙ F.cohomologyPresheaf (n + 1) where
  app T := (pulledCoverSquare f U V hUV T.unop).δ F n (n + 1) rfl
  naturality := sorry

/-- Connecting map `R^n c_*(-|_{U ∩ V}) ⟶ R^{n+1} f_*`, the sheafification of
the Mayer--Vietoris connecting maps of the pulled cover squares along
`sheafPushforward`/`presheafToSheaf` to `Yₑₜ`. -/
noncomputable def boundary (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    higherAlong f (U ⊓ V) n ⟶ relativeHigherDirectImage f (n + 1) where
  app F :=
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
      (boundaryPresheaf f U V hUV n F)
  naturality := sorry

/-- Component of the connecting map on a coefficient sheaf. -/
theorem boundary_app (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (boundary f U V hUV n).app F =
      (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
        (boundaryPresheaf f U V hUV n F) := sorry

/-- A six-term relative Mayer--Vietoris window of higher direct images on `Yₑₜ`. -/
noncomputable def sequence (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ComposableArrows (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) 5 :=
  ComposableArrows.mk₅
    ((toOpens f U V n).app F) ((toIntersection f U V n).app F)
    ((boundary f U V hUV n).app F)
    ((toOpens f U V (n + 1)).app F) ((toIntersection f U V (n + 1)).app F)

/-- The first arrow of a relative Mayer--Vietoris window is the restriction pair. -/
theorem sequence_map_zero (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (sequence f U V hUV n F).map' 0 1 = (toOpens f U V n).app F := sorry

/-- Naturality of the first window arrow in the coefficient sheaf. -/
theorem map_naturality_zero (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    (sequence f U V hUV n F).map' 0 1 ≫
        (higherAlongBiprod f U V n).map φ =
      (relativeHigherDirectImage f n).map φ ≫
        (sequence f U V hUV n G).map' 0 1 := sorry

/-- Naturality of the second window arrow in the coefficient sheaf. -/
theorem map_naturality_one (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    (sequence f U V hUV n F).map' 1 2 ≫ (higherAlong f (U ⊓ V) n).map φ =
      (higherAlongBiprod f U V n).map φ ≫
        (sequence f U V hUV n G).map' 1 2 := sorry

/-- Naturality of the connecting window arrow in the coefficient sheaf. -/
theorem map_naturality_two (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    (sequence f U V hUV n F).map' 2 3 ≫
        (relativeHigherDirectImage f (n + 1)).map φ =
      (higherAlong f (U ⊓ V) n).map φ ≫
        (sequence f U V hUV n G).map' 2 3 := sorry

/-- Naturality of the fourth window arrow in the coefficient sheaf. -/
theorem map_naturality_three (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    (sequence f U V hUV n F).map' 3 4 ≫
        (higherAlongBiprod f U V (n + 1)).map φ =
      (relativeHigherDirectImage f (n + 1)).map φ ≫
        (sequence f U V hUV n G).map' 3 4 := sorry

/-- Naturality of the fifth window arrow in the coefficient sheaf. -/
theorem map_naturality_four (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    (sequence f U V hUV n F).map' 4 5 ≫ (higherAlong f (U ⊓ V) (n + 1)).map φ =
      (higherAlongBiprod f U V (n + 1)).map φ ≫
        (sequence f U V hUV n G).map' 4 5 := sorry

/-- The canonical morphism of relative Mayer--Vietoris windows induced by a
morphism of coefficient sheaves. -/
noncomputable def sequenceMap (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    sequence f U V hUV n F ⟶ sequence f U V hUV n G :=
  ComposableArrows.homMk₅
    ((relativeHigherDirectImage f n).map φ) ((higherAlongBiprod f U V n).map φ)
    ((higherAlong f (U ⊓ V) n).map φ)
    ((relativeHigherDirectImage f (n + 1)).map φ) ((higherAlongBiprod f U V (n + 1)).map φ)
    ((higherAlong f (U ⊓ V) (n + 1)).map φ)
    (map_naturality_zero f U V hUV φ n) (map_naturality_one f U V hUV φ n)
    (map_naturality_two f U V hUV φ n)
    (map_naturality_three f U V hUV φ n) (map_naturality_four f U V hUV φ n)

/-- The window map induced by an identity coefficient morphism is the identity. -/
theorem sequenceMap_id (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    sequenceMap f U V hUV (𝟙 F) n = 𝟙 _ := sorry

/-- Relative Mayer--Vietoris window maps respect composition of coefficient morphisms. -/
theorem sequenceMap_comp (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    {F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (ψ : G ⟶ H) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    sequenceMap f U V hUV (φ ≫ ψ) n =
      sequenceMap f U V hUV φ n ≫ sequenceMap f U V hUV ψ n := sorry

/-- A relative Mayer--Vietoris window as a functor of its coefficient sheaf. -/
noncomputable def sequenceFunctor (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      ComposableArrows (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) 5 where
  obj F := sequence f U V hUV n F
  map φ := sequenceMap f U V hUV φ n
  map_id F := sequenceMap_id f U V hUV F n
  map_comp φ ψ := sequenceMap_comp f U V hUV φ ψ n

/-- The object action of the relative sequence functor is the canonical window. -/
theorem sequenceFunctor_obj (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (sequenceFunctor f U V hUV n).obj F = sequence f U V hUV n F := sorry

/-- The morphism action of the relative sequence functor is the canonical window map. -/
theorem sequenceFunctor_map (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (sequenceFunctor f U V hUV n).map φ = sequenceMap f U V hUV φ n := sorry

/-- For a two-open cover of a scheme, the relative Mayer–Vietoris windows are
exact, including the augmented degree-zero window. The degree-zero relative
direct-image functor is naturally isomorphic to ordinary small-etale pushforward. -/
@[stacks 0EYK]
theorem etaleRelativeMayerVietorisExact (X Y : Scheme.{u}) (f : X ⟶ Y)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    IsIsomorphic (relativeHigherDirectImage f 0)
        ((Scheme.smallEtalePullback f).sheafPushforwardContinuous
          AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology) ∧
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u},
        ((sequence f U V hUV 0 F).zeroPrecomp 1).Exact ∧
          ∀ n : ℕ, (sequence f U V hUV n F).Exact := sorry

/-- Relative Mayer–Vietoris windows are functorial in the abelian coefficient
sheaf, with object and morphism actions given by the canonical window and window map. -/
@[stacks 0EYK]
theorem etaleRelativeMayerVietorisFunctorial (X Y : Scheme.{u}) (f : X ⟶ Y)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (n : ℕ) {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (sequenceFunctor f U V hUV n).obj F = sequence f U V hUV n F ∧
      (sequenceFunctor f U V hUV n).map φ = sequenceMap f U V hUV φ n := sorry

end EtaleRelativeMayerVietoris
