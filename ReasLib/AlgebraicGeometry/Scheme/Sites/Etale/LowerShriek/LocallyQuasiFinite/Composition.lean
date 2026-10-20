/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PresheafPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Pullback

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
    lowerShriek (f' ≫ g) ⟶ lowerShriek f' ⋙ smallEtalePushforwardAb g where
  app F := sheafifyPresheafPushforward g (lowerShriekPresheafComp_app f' g F)
  naturality := sorry

/-- The sheafified comparison at an abelian étale sheaf `F`. -/
def lowerShriekCompToPushforward_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f' ≫ g)).obj F ⟶
      (smallEtalePushforwardAb g).obj ((lowerShriek f').obj F) :=
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

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private proof to the public comparison.
set_option backward.privateInPublic true in
/-- The sheafified composition comparison takes values in compactly supported sections. -/
private theorem lowerShriekCompToPushforward_mem
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : ((lowerShriek (f' ≫ g)).obj F).obj.obj (op V)) :
    (((lowerShriekCompToPushforward f' g).app F).hom.app (op V)).hom σ ∈
      compactSupportSections g ((lowerShriek f').obj F) V :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private proof to the public comparison.
set_option backward.privateInPublic true in
/-- Restricting the composition comparison to compact support commutes with restriction. -/
private theorem lowerShriekComp_sections_naturality
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V W : Y.Etaleᵒᵖ} (a : V ⟶ W) :
    ((lowerShriek (f' ≫ g)).obj F).obj.map a ≫
        AddCommGrpCat.ofHom
          ((((lowerShriekCompToPushforward f' g).app F).hom.app W).hom.codRestrict
            (compactSupportSections g ((lowerShriek f').obj F) W.unop)
            (lowerShriekCompToPushforward_mem f' g F W.unop)) =
      AddCommGrpCat.ofHom
          ((((lowerShriekCompToPushforward f' g).app F).hom.app V).hom.codRestrict
            (compactSupportSections g ((lowerShriek f').obj F) V.unop)
            (lowerShriekCompToPushforward_mem f' g F V.unop)) ≫
        (etaleLowerShriekPresheaf g ((lowerShriek f').obj F)).map a :=
  sorry

-- Local declaration justification (metaprogramming implementation): the comparison uses
-- its private support-membership and naturality proofs.
set_option backward.privateInPublic true in
/-- The compact-support restriction of the composition comparison is natural in coefficients. -/
private theorem lowerShriekComp_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    (lowerShriek (f' ≫ g)).map α ≫
        (ObjectProperty.homMk
          { app := fun V ↦ AddCommGrpCat.ofHom
              ((((lowerShriekCompToPushforward f' g).app G).hom.app V).hom.codRestrict
                (compactSupportSections g ((lowerShriek f').obj G) V.unop)
                (lowerShriekCompToPushforward_mem f' g G V.unop))
            naturality := fun _ _ a ↦ lowerShriekComp_sections_naturality f' g G a } :
          (lowerShriek (f' ≫ g)).obj G ⟶
            (etaleLowerShriek g).obj ((lowerShriek f').obj G)) =
      (ObjectProperty.homMk
          { app := fun V ↦ AddCommGrpCat.ofHom
              ((((lowerShriekCompToPushforward f' g).app F).hom.app V).hom.codRestrict
                (compactSupportSections g ((lowerShriek f').obj F) V.unop)
                (lowerShriekCompToPushforward_mem f' g F V.unop))
            naturality := fun _ _ a ↦ lowerShriekComp_sections_naturality f' g F a } :
          (lowerShriek (f' ≫ g)).obj F ⟶
            (etaleLowerShriek g).obj ((lowerShriek f').obj F)) ≫
        (lowerShriek f' ⋙ etaleLowerShriek g).map α :=
  sorry

-- Local declaration justification (metaprogramming implementation): the comparison uses
-- its private support-membership and naturality proofs.
set_option backward.privateInPublic true in
/-- The canonical mixed composition comparison, obtained by restricting the
sheafified finite-support map to the compact-support subgroup. -/
def lowerShriekComp :
    lowerShriek (f' ≫ g) ⟶ lowerShriek f' ⋙ etaleLowerShriek g :=
  { app := fun F ↦
      ObjectProperty.homMk
        { app := fun V ↦ AddCommGrpCat.ofHom
            ((((lowerShriekCompToPushforward f' g).app F).hom.app V).hom.codRestrict
              (compactSupportSections g ((lowerShriek f').obj F) V.unop)
              (lowerShriekCompToPushforward_mem f' g F V.unop))
          naturality := fun _ _ a ↦ lowerShriekComp_sections_naturality f' g F a }
    naturality := fun _ _ α ↦ lowerShriekComp_naturality f' g α }

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

/-- The sheafified finite-support comparison factors through the compact-support inclusion. -/
theorem lowerShriekComp_factors :
    MonoOver.Factors
      (MonoOver.mk (whiskerLeft (lowerShriek f') (etaleLowerShriekι g)))
      (lowerShriekCompToPushforward f' g) :=
  ⟨lowerShriekComp f' g, lowerShriekComp_ι f' g⟩

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
`f' ≫ g` along `X₁ ⊂ X`, then the mixed composition
comparison. -/
def lowerShriekCompIso_openImmersion_outer :
    etaleRestrictionSheaf a AddCommGrpCat.{u} ⋙ lowerShriek (a ≫ f' ≫ g) ⟶
      lowerShriek f' ⋙ etaleLowerShriek g :=
  lowerShriekOpenImmersion a (f' ≫ g) ≫ lowerShriekComp f' g

/-- Inner path of the open-immersion covariance square: reassociate along the
cartesian square, apply the mixed comparison of `f₁'` with `j' ≫ g`, cross
the base-change locality isomorphism of `f'_!` on the base, then covariance
of `g_!` along `Y₁' ⊂ Y'`. -/
def lowerShriekCompIso_openImmersion_inner :
    etaleRestrictionSheaf a AddCommGrpCat.{u} ⋙ lowerShriek (a ≫ f' ≫ g) ⟶
      lowerShriek f' ⋙ etaleLowerShriek g :=
  whiskerLeft (etaleRestrictionSheaf a AddCommGrpCat.{u})
      ((lowerShriekCongr (lowerShriekComp_openImmersion_comp_eq f' g a f₁' j' h_cart)).hom ≫
        lowerShriekComp f₁' (j' ≫ g)) ≫
    (Functor.associator (etaleRestrictionSheaf a AddCommGrpCat.{u})
        (lowerShriek f₁') (etaleLowerShriek (j' ≫ g))).hom ≫
    whiskerRight
      (whiskerRight (etaleRestrictionSheafIsoPullback a).hom (lowerShriek f₁'))
      (etaleLowerShriek (j' ≫ g)) ≫
    whiskerRight (lowerShriekBaseChangeIso f' j' f₁' a h_cart).inv
      (etaleLowerShriek (j' ≫ g)) ≫
    (Functor.associator (lowerShriek f') (etaleAbelianSheafPullback j')
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
    (Functor.associator (lowerShriek f') (etaleLowerShriek g)
        (etaleAbelianSheafPullback b)).hom ≫
    whiskerLeft (lowerShriek f') (etaleLowerShriekBaseChange g b g₁ b' h_lower) ≫
    (Functor.associator (lowerShriek f') (etaleAbelianSheafPullback b')
        (etaleLowerShriek g₁)).inv ≫
    whiskerRight (lowerShriekBaseChange f' b' f₁' a h_upper) (etaleLowerShriek g₁) ≫
    (Functor.associator (etaleAbelianSheafPullback a) (lowerShriek f₁')
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

section separated

variable [IsSeparated f']

/-- Left-hand identification of the mixed composition comparison with the
separated composition isomorphism, via the sheafified finite-support identification. -/
def lowerShriekCompIso_separated_left :
    lowerShriek (f' ≫ g) ⟶ etaleLowerShriek f' ⋙ etaleLowerShriek g :=
  (lowerShriekIso_separated (f' ≫ g)).hom ≫ (etaleLowerShriekCompIso f' g).inv

/-- Right-hand identification of the mixed composition comparison with the
separated composition isomorphism, via the sheafified finite-support identification on
`f'`. -/
def lowerShriekCompIso_separated_right :
    lowerShriek (f' ≫ g) ⟶ etaleLowerShriek f' ⋙ etaleLowerShriek g :=
  lowerShriekComp f' g ≫
    whiskerRight (lowerShriekIso_separated f').hom (etaleLowerShriek g)

end separated

section openImmersion

variable {X₁ Y₁' : Scheme.{u}} (a : X₁ ⟶ X) (f₁' : X₁ ⟶ Y₁') (j' : Y₁' ⟶ Y')
variable (h_cart : IsPullback a f₁' f' j')
variable [IsOpenImmersion a] [IsOpenImmersion j']
variable [LocallyQuasiFinite f₁'] [LocallyOfFiniteType f₁']
variable [LocallyQuasiFinite (f₁' ≫ j' ≫ g)] [LocallyOfFiniteType (f₁' ≫ j' ≫ g)]
variable [LocallyQuasiFinite (a ≫ f' ≫ g)] [LocallyOfFiniteType (a ≫ f' ≫ g)]
variable [IsSeparated (j' ≫ g)] [LocallyOfFiniteType (j' ≫ g)]

/-- Mixed composition respects covariance along open immersions. -/
@[stacks 0F79]
theorem lowerShriekCompIso_openImmersion :
    lowerShriekCompIso_openImmersion_inner f' g a f₁' j' h_cart =
      lowerShriekCompIso_openImmersion_outer f' g a :=
  sorry

end openImmersion

section baseChange

variable {X₁ Y₁' Y₁ : Scheme.{u}}
variable (f₁' : X₁ ⟶ Y₁') (g₁ : Y₁' ⟶ Y₁) (b : Y₁ ⟶ Y)
variable (b' : Y₁' ⟶ Y') (a : X₁ ⟶ X)
variable (h_upper : IsPullback a f₁' f' b') (h_lower : IsPullback b' g₁ g b)
variable [LocallyQuasiFinite f₁'] [LocallyOfFiniteType f₁']
variable [LocallyQuasiFinite (f₁' ≫ g₁)] [LocallyOfFiniteType (f₁' ≫ g₁)]
variable [IsSeparated g₁] [LocallyOfFiniteType g₁]

/-- Mixed composition commutes with arbitrary cartesian base change. -/
@[stacks 0F79]
theorem lowerShriekCompIso_baseChange :
    lowerShriekCompIso_baseChange_inner f' g f₁' g₁ b b' a h_upper h_lower =
      lowerShriekCompIso_baseChange_outer f' g f₁' g₁ b b' a h_upper h_lower :=
  sorry

end baseChange

section separated

variable [IsSeparated f']

/-- For separated first morphisms, mixed composition agrees with compact-support composition. -/
@[stacks 0F79]
theorem lowerShriekCompIso_separated :
    lowerShriekCompIso_separated_left f' g =
      lowerShriekCompIso_separated_right f' g :=
  sorry

end separated


/-- For separated first morphisms, composition of the separated identifications
constructs a mixed composition isomorphism. -/
private def lowerShriekCompSeparatedIso [IsSeparated f'] :
    lowerShriek (f' ≫ g) ≅ lowerShriek f' ⋙ etaleLowerShriek g :=
  lowerShriekIso_separated (f' ≫ g) ≪≫
    (etaleLowerShriekCompIso f' g).symm ≪≫
    isoWhiskerRight (lowerShriekIso_separated f').symm (etaleLowerShriek g)

/-- The separated composition construction has the canonical forward map. -/
private theorem lowerShriekCompSeparatedIso_hom [IsSeparated f'] :
    (lowerShriekCompSeparatedIso f' g).hom = lowerShriekComp f' g := by
  apply (cancel_mono
    (whiskerRight (lowerShriekIso_separated f').hom (etaleLowerShriek g))).1
  simpa [lowerShriekCompSeparatedIso, lowerShriekCompIso_separated_left,
    lowerShriekCompIso_separated_right, Category.assoc, ← whiskerRight_comp] using
      lowerShriekCompIso_separated f' g

/-- Mixed composition becomes an explicitly constructed isomorphism after pullback
to the spectrum of an algebraically closed field. -/
private def lowerShriekCompGeometricPullbackIso
    {K : Type u} [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ Y) :
    lowerShriek (f' ≫ g) ⋙ etaleAbelianSheafPullback b ≅
      (lowerShriek f' ⋙ etaleLowerShriek g) ⋙ etaleAbelianSheafPullback b := by
  let b' := pullback.fst g b
  let g₁ := pullback.snd g b
  let a := pullback.fst f' b'
  let f₁' := pullback.snd f' b'
  have h_upper : IsPullback a f₁' f' b' := IsPullback.of_hasPullback f' b'
  have h_lower : IsPullback b' g₁ g b := IsPullback.of_hasPullback g b
  have : LocallyQuasiFinite (f₁' ≫ g₁) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite)
      (h_upper.paste_vert h_lower) inferInstance
  have : LocallyOfFiniteType (f₁' ≫ g₁) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (h_upper.paste_vert h_lower) inferInstance
  have : IsSeparated (f₁' ≫ g₁) := inferInstance
  have : IsSeparated f₁' := IsSeparated.of_comp f₁' g₁
  let J : (lowerShriek f' ⋙ etaleLowerShriek g) ⋙ etaleAbelianSheafPullback b ≅
      etaleAbelianSheafPullback a ⋙ lowerShriek f₁' ⋙ etaleLowerShriek g₁ :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (lowerShriek f') (asIso (etaleLowerShriekBaseChange g b g₁ b' h_lower)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (lowerShriekBaseChangeIso f' b' f₁' a h_upper)
        (etaleLowerShriek g₁) ≪≫
      Functor.associator _ _ _
  exact lowerShriekBaseChangeIso (f' ≫ g) b (f₁' ≫ g₁) a
      (h_upper.paste_vert h_lower) ≪≫
    isoWhiskerLeft (etaleAbelianSheafPullback a)
      (lowerShriekCompSeparatedIso f₁' g₁) ≪≫ J.symm

/-- The geometric pullback construction identifies the actual pulled-back comparison. -/
private theorem lowerShriekCompGeometricPullbackIso_hom
    {K : Type u} [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ Y) :
    (lowerShriekCompGeometricPullbackIso f' g b).hom =
      whiskerRight (lowerShriekComp f' g) (etaleAbelianSheafPullback b) := by
  let b' := pullback.fst g b
  let g₁ := pullback.snd g b
  let a := pullback.fst f' b'
  let f₁' := pullback.snd f' b'
  have h_upper : IsPullback a f₁' f' b' := IsPullback.of_hasPullback f' b'
  have h_lower : IsPullback b' g₁ g b := IsPullback.of_hasPullback g b
  have : LocallyQuasiFinite (f₁' ≫ g₁) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite)
      (h_upper.paste_vert h_lower) inferInstance
  have : LocallyOfFiniteType (f₁' ≫ g₁) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (h_upper.paste_vert h_lower) inferInstance
  have : IsSeparated (f₁' ≫ g₁) := inferInstance
  have : IsSeparated f₁' := IsSeparated.of_comp f₁' g₁
  let J : (lowerShriek f' ⋙ etaleLowerShriek g) ⋙ etaleAbelianSheafPullback b ≅
      etaleAbelianSheafPullback a ⋙ lowerShriek f₁' ⋙ etaleLowerShriek g₁ :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (lowerShriek f') (asIso (etaleLowerShriekBaseChange g b g₁ b' h_lower)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (lowerShriekBaseChangeIso f' b' f₁' a h_upper)
        (etaleLowerShriek g₁) ≪≫ Functor.associator _ _ _
  apply (cancel_mono J.hom).1
  change (((lowerShriekBaseChangeIso (f' ≫ g) b (f₁' ≫ g₁) a
        (h_upper.paste_vert h_lower)).hom ≫
      whiskerLeft (etaleAbelianSheafPullback a)
        (lowerShriekCompSeparatedIso f₁' g₁).hom) ≫ J.inv) ≫ J.hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, lowerShriekCompSeparatedIso_hom]
  exact (lowerShriekCompIso_baseChange f' g f₁' g₁ b b' a h_upper h_lower).symm

/-- The inverse-image stalk identification is natural for the mixed comparison. -/
private theorem lowerShriekComp_stalk_pullback
    {T : Scheme.{u}} (b : T ⟶ Y) (z : GeometricPoint T)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (GeometricPoint.toSmallEtalePoint (z.map b)).sheafFiber.map
        ((lowerShriekComp f' g).app F) ≫
      (pullbackSheafFiberIso b z ((lowerShriek f' ⋙ etaleLowerShriek g).obj F)).hom =
    (pullbackSheafFiberIso b z ((lowerShriek (f' ≫ g)).obj F)).hom ≫
      (GeometricPoint.toSmallEtalePoint z).sheafFiber.map
        ((etaleAbelianSheafPullback b).map ((lowerShriekComp f' g).app F)) :=
  sorry

/-- The mixed composition comparison is invertible, as detected by geometric stalks. -/
instance lowerShriekComp_isIso : IsIso (lowerShriekComp f' g) := by
  have component (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
      IsIso ((lowerShriekComp f' g).app F) := by
    let s (y : Y) : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) _)) ≫
        Y.fromSpecResidueField y
    have hs : ⋃ y, Set.range (s y) = Set.univ := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨y, default, Y.fromSpecResidueField_apply y _⟩
    let P := ObjectProperty.ofObj (fun y ↦ pointSmallEtale (s y))
    have hP : P.IsConservativeFamilyOfPoints := isConservative_pointSmallEtale s hs
    apply ((hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff
      ((lowerShriekComp f' g).app F)).2
    rintro ⟨p, hp⟩
    obtain ⟨y⟩ := hp
    let K := AlgebraicClosure (Y.residueField y)
    let z : GeometricPoint (Spec (.of K)) := GeometricPoint.of K (𝟙 _)
    let α := (lowerShriekComp f' g).app F
    have pulled : IsIso ((etaleAbelianSheafPullback (s y)).map α) := by
      change IsIso ((whiskerRight (lowerShriekComp f' g)
        (etaleAbelianSheafPullback (s y))).app F)
      rw [← lowerShriekCompGeometricPullbackIso_hom]
      infer_instance
    have stalk_eq :
        (GeometricPoint.toSmallEtalePoint (z.map (s y))).sheafFiber.map α =
          (pullbackSheafFiberIso (s y) z ((lowerShriek (f' ≫ g)).obj F)).hom ≫
            (GeometricPoint.toSmallEtalePoint z).sheafFiber.map
              ((etaleAbelianSheafPullback (s y)).map α) ≫
            (pullbackSheafFiberIso (s y) z
              ((lowerShriek f' ⋙ etaleLowerShriek g).obj F)).inv := by
      apply (cancel_mono (pullbackSheafFiberIso (s y) z
        ((lowerShriek f' ⋙ etaleLowerShriek g).obj F)).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        lowerShriekComp_stalk_pullback f' g (s y) z F
    have : IsIso ((GeometricPoint.toSmallEtalePoint (z.map (s y))).sheafFiber.map α) := by
      rw [stalk_eq]
      infer_instance
    have hz : GeometricPoint.toSmallEtalePoint (z.map (s y)) =
        pointSmallEtale (s y) := by
      change pointSmallEtale ((𝟙 (Spec (.of K))) ≫ s y) = pointSmallEtale (s y)
      simp only [Category.id_comp]
    rw [hz] at this
    exact this
  exact NatIso.isIso_of_isIso_app (lowerShriekComp f' g)

/-- Direct image with finite support along a composite is naturally isomorphic to
finite-support direct image followed by compact-support direct image. -/
@[stacks 0F79]
def lowerShriekCompIso :
    lowerShriek (f' ≫ g) ≅ lowerShriek f' ⋙ etaleLowerShriek g :=
  asIso (lowerShriekComp f' g)

/-- The mixed composition identification evaluated at an abelian étale sheaf. -/
def lowerShriekCompIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f' ≫ g)).obj F ≅
      (etaleLowerShriek g).obj ((lowerShriek f').obj F) :=
  (lowerShriekCompIso f' g).app F

/-- The forward map of the mixed composition isomorphism is the finite-support comparison. -/
theorem lowerShriekCompIso_hom :
    (lowerShriekCompIso f' g).hom = lowerShriekComp f' g :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
