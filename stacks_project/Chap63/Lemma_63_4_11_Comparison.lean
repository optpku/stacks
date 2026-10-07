module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import stacks_project.Chap63.Definition_63_4_4_LowerShriek
public import stacks_project.Chap63.Lemma_63_3_12_Comparison
public import stacks_project.Chap63.Lemma_63_4_10
public import stacks_project.Chap63.Lemma_63_4_10_Comparison
public import stacks_project.Chap63.Lemma_63_4_11_Pullback
public import stacks_project.Chap63.Remark_63_3_14_Comparison
public import stacks_project.Chap63.Remark_63_4_6_Covariance_with_respect_to_open_embeddings_OpenImmersion
public import stacks_project.Chap63.Remark_63_4_9_Pushforward

/-!
# Mixed composition comparison for locally quasi-finite lower shriek

For composable scheme maps `f' : X ⟶ Y'` and `g : Y' ⟶ Y` with `f'` and
`f' ≫ g` locally quasi-finite and `g` separated and locally of finite type,
finite-support formal sums on `X_V` determine a presheaf map
`c : f_{p!} ⟶ g_* f'_{p!}`, which sheafifies to `c^# : f_! ⟶ g_* f'_!` and
factors uniquely through `g_! ⊂ g_*` as `c' : f_! ⟶ g_! ∘ f'_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale.FiniteSupport
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y' Y : Scheme.{u}} (f' : X ⟶ Y') (g : Y' ⟶ Y)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [LocallyQuasiFinite (f' ≫ g)] [LocallyOfFiniteType (f' ≫ g)]
variable [IsSeparated g] [LocallyOfFiniteType g]

/-- The source map `c : f_{p!} ⟶ g_* f'_{p!}` of abelian étale presheaves,
obtained by transporting finite-support colimits along
`smallEtalePullbackCompIso`. -/
def lowerShriekPresheafComp :
    lowerShriekPresheaf (f' ≫ g) ⟶
      lowerShriekPresheaf f' ⋙ presheafPushforwardAb g where
  app F :=
    { app := fun V ↦
        colimMap (diagramComp f' g F V.unop) ≫
          colimit.pre
            (diagram f' F ((smallEtalePullback g).obj V.unop))
            (Admissible.compFunctor f' g V.unop)
      naturality := sorry }
  naturality := sorry

/-- Evaluating the presheaf comparison at an abelian étale sheaf `F`. -/
def lowerShriekPresheafComp_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekPresheaf (f' ≫ g)).obj F ⟶
      (presheafPushforwardAb g).obj ((lowerShriekPresheaf f').obj F) :=
  (lowerShriekPresheafComp f' g).app F

/-- The presheaf comparison sends the class of a finite-support pair to the
class of the same pair viewed on `X_{V'}`. -/
theorem lowerShriekPresheafComp_ofTerm
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (t : FiniteSupportTerm (f' ≫ g) F V) :
    ((lowerShriekPresheafComp_app f' g F).app (op V)).hom
        (ofTerm (f' ≫ g) F V t) =
      ofTerm f' F ((smallEtalePullback g).obj V)
        (FiniteSupportTerm.comp f' g t) :=
  sorry

/-- The presheaf comparison sends a finite formal sum of pairs on `X_V` to the
same formal sum of pairs viewed on `X_{V'}`. -/
theorem lowerShriekPresheafComp_ofFormalSum
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (s : FiniteSupportFormalSum (f' ≫ g) F V) :
    ((lowerShriekPresheafComp_app f' g F).app (op V)).hom
        (ofFormalSum (f' ≫ g) F V s) =
      ofFormalSum f' F ((smallEtalePullback g).obj V)
        (FreeAbelianGroup.map (FiniteSupportTerm.comp f' g) s) :=
  sorry

/-- The sheafified comparison `c^# : f_! ⟶ g_* f'_!` obtained from
`lowerShriekPresheafComp`. -/
def lowerShriekCompToPushforward :
    lowerShriek (f' ≫ g) ⟶ lowerShriek f' ⋙ etaleAbelianPushforward g where
  app F := sheafifyPresheafPushforward g (lowerShriekPresheafComp_app f' g F)
  naturality := sorry

/-- The sheafified comparison at an abelian étale sheaf `F`. -/
def lowerShriekCompToPushforward_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f' ≫ g)).obj F ⟶
      (etaleAbelianPushforward g).obj ((lowerShriek f').obj F) :=
  (lowerShriekCompToPushforward f' g).app F

/-- Objectwise, `c^#` is `sheafifyPresheafPushforward` of the presheaf map
`c`. -/
theorem lowerShriekCompToPushforward_app_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekCompToPushforward_app f' g F =
      sheafifyPresheafPushforward g (lowerShriekPresheafComp_app f' g F) :=
  sorry

/-- Whiskering the compact-support inclusion `g_! ⟶ g_*` on the left by
`f'_!` remains a monomorphism. -/
instance lowerShriekComp_ι_mono :
    Mono (whiskerLeft (lowerShriek f') (etaleLowerShriekι g)) :=
  sorry

/-- The sheafified comparison `c^#` factors through the compact-support
inclusion `g_! ⟶ g_*`. -/
theorem lowerShriekComp_factors :
    MonoOver.Factors
      (MonoOver.mk (whiskerLeft (lowerShriek f') (etaleLowerShriekι g)))
      (lowerShriekCompToPushforward f' g) :=
  sorry

/-- The canonical comparison `c' : f_! ⟶ g_! ∘ f'_!` obtained by uniquely
factoring `c^#` through `etaleLowerShriekι g`. -/
def lowerShriekComp :
    lowerShriek (f' ≫ g) ⟶ lowerShriek f' ⋙ etaleLowerShriek g :=
  MonoOver.factorThru
    (MonoOver.mk (whiskerLeft (lowerShriek f') (etaleLowerShriekι g)))
    (lowerShriekCompToPushforward f' g) (lowerShriekComp_factors f' g)

/-- The comparison fills the triangle with the compact-support inclusion of
`g_!`. -/
theorem lowerShriekComp_ι :
    lowerShriekComp f' g ≫ whiskerLeft (lowerShriek f') (etaleLowerShriekι g) =
      lowerShriekCompToPushforward f' g :=
  sorry

/-- Any morphism making the compact-support triangle commute equals the
canonical comparison. -/
theorem lowerShriekComp_lift_unique
    (α : lowerShriek (f' ≫ g) ⟶ lowerShriek f' ⋙ etaleLowerShriek g)
    (hα : α ≫ whiskerLeft (lowerShriek f') (etaleLowerShriekι g) =
      lowerShriekCompToPushforward f' g) :
    α = lowerShriekComp f' g :=
  sorry

/-- The comparison `f_! ⟶ g_! ∘ f'_!` is an isomorphism. -/
instance lowerShriekComp_isIso : IsIso (lowerShriekComp f' g) :=
  sorry

/-- Site-level adjunction `etaleRestriction ⊣ smallEtalePullback` along an
open immersion. -/
def etaleOpenImmersionSiteAdj {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    etaleRestriction j ⊣ smallEtalePullback j :=
  MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ j inferInstance trivial

/-- The open-immersion site adjunction is `Over.mapPullbackAdj` for étale
morphisms. -/
theorem etaleOpenImmersionSiteAdj_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    etaleOpenImmersionSiteAdj j =
      MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ j inferInstance trivial :=
  sorry

/-- Restriction of abelian étale sheaves along an open immersion agrees with
small-étale inverse image. -/
def etaleRestrictionSheafIsoPullback {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ≅ etaleAbelianSheafPullback j :=
  ((Adjunction.sheafPushforwardContinuous (etaleOpenImmersionSiteAdj j)
        U.smallEtaleTopology X.smallEtaleTopology :
      etaleRestrictionSheaf j AddCommGrpCat.{u} ⊣
        (smallEtalePullback j).sheafPushforwardContinuous AddCommGrpCat.{u}
          X.smallEtaleTopology U.smallEtaleTopology).leftAdjointUniq
    ((smallEtalePullback j).sheafAdjunctionContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology U.smallEtaleTopology))

/-- The open-immersion restriction/pullback comparison at an abelian étale
sheaf. -/
def etaleRestrictionSheafIsoPullback_app {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F ≅
      (etaleAbelianSheafPullback j).obj F :=
  (etaleRestrictionSheafIsoPullback j).app F

/-- The objectwise comparison is the component of
`etaleRestrictionSheafIsoPullback`. -/
theorem etaleRestrictionSheafIsoPullback_app_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleRestrictionSheafIsoPullback_app j F =
      (etaleRestrictionSheafIsoPullback j).app F :=
  sorry

section openImmersion

variable {X₁ Y₁' : Scheme.{u}} (a : X₁ ⟶ X) (f₁' : X₁ ⟶ Y₁') (j' : Y₁' ⟶ Y')
variable (h_cart : IsPullback a f₁' f' j')
variable [IsOpenImmersion a] [IsOpenImmersion j']
variable [LocallyQuasiFinite f₁'] [LocallyOfFiniteType f₁']
variable [LocallyQuasiFinite (f₁' ≫ j' ≫ g)] [LocallyOfFiniteType (f₁' ≫ j' ≫ g)]
variable [LocallyQuasiFinite (a ≫ f' ≫ g)] [LocallyOfFiniteType (a ≫ f' ≫ g)]
variable [IsSeparated (j' ≫ g)] [LocallyOfFiniteType (j' ≫ g)]

/-- The cartesian square identifies the two composites `X₁ ⟶ Y`. -/
theorem lowerShriekComp_openImmersion_comp_eq
    (h_cart : IsPullback a f₁' f' j') :
    a ≫ f' ≫ g = f₁' ≫ j' ≫ g :=
  sorry

/-- Outer path of the open-immersion covariance square: covariance of
`f' ≫ g` along `X₁ ⊂ X` as in Remark 63.4.6, then the mixed composition
comparison. -/
def lowerShriekCompIso_openImmersion_outer :
    etaleRestrictionSheaf a AddCommGrpCat.{u} ⋙ lowerShriek (a ≫ f' ≫ g) ⟶
      lowerShriek f' ⋙ etaleLowerShriek g :=
  lowerShriekOpenImmersion a (f' ≫ g) ≫ lowerShriekComp f' g

/-- Inner path of the open-immersion covariance square: reassociate along the
cartesian square, apply the mixed comparison of `f₁'` with `j' ≫ g`, cross
the Lemma 63.4.10 locality isomorphism of `f'_!` on the base, then covariance
of `g_!` along `Y₁' ⊂ Y'` as in Remark 63.3.5. -/
def lowerShriekCompIso_openImmersion_inner :
    etaleRestrictionSheaf a AddCommGrpCat.{u} ⋙ lowerShriek (a ≫ f' ≫ g) ⟶
      lowerShriek f' ⋙ etaleLowerShriek g :=
  whiskerLeft (etaleRestrictionSheaf a AddCommGrpCat.{u})
      ((lowerShriekCongr (lowerShriekComp_openImmersion_comp_eq f' g a f₁' j' h_cart)).hom ≫
        lowerShriekComp f₁' (j' ≫ g)) ≫
    (associator (etaleRestrictionSheaf a AddCommGrpCat.{u})
        (lowerShriek f₁') (etaleLowerShriek (j' ≫ g))).hom ≫
    whiskerRight
      (whiskerRight (etaleRestrictionSheafIsoPullback a).hom (lowerShriek f₁'))
      (etaleLowerShriek (j' ≫ g)) ≫
    whiskerRight (lowerShriekBaseChangeIso f' j' f₁' a h_cart).inv
      (etaleLowerShriek (j' ≫ g)) ≫
    (associator (lowerShriek f') (etaleAbelianSheafPullback j')
        (etaleLowerShriek (j' ≫ g))).inv ≫
    whiskerLeft (lowerShriek f')
      (whiskerRight (etaleRestrictionSheafIsoPullback j').inv
          (etaleLowerShriek (j' ≫ g)) ≫
        etaleLowerShriekOpenImmersion j' g)

end openImmersion

section baseChange

variable {X₁ Y₁' Y₁ : Scheme.{u}}
variable (f₁' : X₁ ⟶ Y₁') (g₁ : Y₁' ⟶ Y₁) (b : Y₁ ⟶ Y)
variable (b' : Y₁' ⟶ Y') (a : X₁ ⟶ X)
variable (h_upper : IsPullback a f₁' f' b') (h_lower : IsPullback b' g₁ g b)
variable [LocallyQuasiFinite f₁'] [LocallyOfFiniteType f₁']
variable [LocallyQuasiFinite (f₁' ≫ g₁)] [LocallyOfFiniteType (f₁' ≫ g₁)]
variable [IsSeparated g₁] [LocallyOfFiniteType g₁]

/-- Two-step path of the pasted base-change square: the mixed composition
comparison, then the compact-support base change of `g`, then the locally
quasi-finite base change of `f'`. -/
def lowerShriekCompIso_baseChange_inner :
    lowerShriek (f' ≫ g) ⋙ etaleAbelianSheafPullback b ⟶
      etaleAbelianSheafPullback a ⋙ lowerShriek f₁' ⋙ etaleLowerShriek g₁ :=
  whiskerRight (lowerShriekComp f' g) (etaleAbelianSheafPullback b) ≫
    (associator (lowerShriek f') (etaleLowerShriek g)
        (etaleAbelianSheafPullback b)).hom ≫
    whiskerLeft (lowerShriek f') (etaleLowerShriekBaseChange g b g₁ b' h_lower) ≫
    (associator (lowerShriek f') (etaleAbelianSheafPullback b')
        (etaleLowerShriek g₁)).inv ≫
    whiskerRight (lowerShriekBaseChange f' b' f₁' a h_upper) (etaleLowerShriek g₁) ≫
    (associator (etaleAbelianSheafPullback a) (lowerShriek f₁')
        (etaleLowerShriek g₁)).hom

/-- Outer path of the pasted base-change square: base change of `f' ≫ g` along
the pasted cartesian square, then the mixed composition comparison of `f₁'`
and `g₁`. -/
def lowerShriekCompIso_baseChange_outer :
    lowerShriek (f' ≫ g) ⋙ etaleAbelianSheafPullback b ⟶
      etaleAbelianSheafPullback a ⋙ lowerShriek f₁' ⋙ etaleLowerShriek g₁ :=
  lowerShriekBaseChange (f' ≫ g) b (f₁' ≫ g₁) a (h_upper.paste_vert h_lower) ≫
    whiskerLeft (etaleAbelianSheafPullback a) (lowerShriekComp f₁' g₁)

end baseChange

/-- The sheafified finite-support comparison `lowerShriek h ⟶ etaleLowerShriek h`,
obtained from `lowerShriekPresheafIsoHom`. -/
def lowerShriekToEtaleLowerShriek_411 {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    lowerShriek h ⟶ etaleLowerShriek h :=
  whiskerRight (lowerShriekPresheafIsoHom h)
      (presheafToSheaf T.smallEtaleTopology AddCommGrpCat.{u}) ≫
    (associator (etaleLowerShriek h)
        (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u})
        (presheafToSheaf T.smallEtaleTopology AddCommGrpCat.{u})).hom ≫
    whiskerLeft (etaleLowerShriek h)
      (asIso
        (sheafificationAdjunction T.smallEtaleTopology
          AddCommGrpCat.{u}).counit).hom ≫
    (rightUnitor (etaleLowerShriek h)).hom

/-- The sheafified finite-support comparison is an isomorphism. -/
instance lowerShriekToEtaleLowerShriek_411_isIso {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    IsIso (lowerShriekToEtaleLowerShriek_411 h) :=
  sorry

/-- Sheafification of Lemma 63.4.1: if `h` is separated and locally
quasi-finite, then `lowerShriek h` agrees with `etaleLowerShriek h`. -/
def lowerShriekIso_separated {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    lowerShriek h ≅ etaleLowerShriek h :=
  asIso (lowerShriekToEtaleLowerShriek_411 h)

/-- The forward map of `lowerShriekIso_separated` is the sheafified
finite-support comparison. -/
theorem lowerShriekIso_separated_hom {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    (lowerShriekIso_separated h).hom = lowerShriekToEtaleLowerShriek_411 h :=
  sorry

section separated

variable [IsSeparated f']

/-- Left-hand identification of the mixed composition comparison with the
separated composition isomorphism, via sheafification of Lemma 63.4.1. -/
def lowerShriekCompIso_separated_left :
    lowerShriek (f' ≫ g) ⟶ etaleLowerShriek f' ⋙ etaleLowerShriek g :=
  (lowerShriekIso_separated (f' ≫ g)).hom ≫ (etaleLowerShriekCompIso f' g).inv

/-- Right-hand identification of the mixed composition comparison with the
separated composition isomorphism, via sheafification of Lemma 63.4.1 on
`f'`. -/
def lowerShriekCompIso_separated_right :
    lowerShriek (f' ≫ g) ⟶ etaleLowerShriek f' ⋙ etaleLowerShriek g :=
  lowerShriekComp f' g ≫
    whiskerRight (lowerShriekIso_separated f').hom (etaleLowerShriek g)

end separated

end AlgebraicGeometry.Scheme.Etale

end
