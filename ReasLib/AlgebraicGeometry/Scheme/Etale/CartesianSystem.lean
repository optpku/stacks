/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Cartesian étale systems over a diagram of schemes

An object of `lim_i X_{i,étale}` is a family of étale morphisms `U_i ⟶ X_i` whose transition
squares are cartesian. Pullback from `X.Etale` and the canonical coproduct comparison
`∐ X_i ⟶ X` are the comparison data for scheme-to-algebraic-space colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

universe u v

/-- A cartesian étale system over a diagram `D : J ⥤ Over S` is a family of schemes `U_i` with
étale maps `U_i ⟶ X_i` and cartesian transition squares. -/
structure CartesianEtaleSystem {J : Type v} [Category.{v} J] {S : Scheme.{u}}
    (D : J ⥤ Over S) where
  /-- The diagram of schemes `i ↦ U_i`. -/
  functor : J ⥤ Scheme.{u}
  /-- The natural family of morphisms `U_i ⟶ X_i`. -/
  π : functor ⟶ D ⋙ Over.forget S
  /-- Each morphism `U_i ⟶ X_i` is étale. -/
  etale : ∀ i, Etale (π.app i)
  /-- Each transition square is a pullback. -/
  isPullback : ∀ {i j : J} (hij : i ⟶ j),
    IsPullback (functor.map hij) (π.app i) (π.app j) (D.map hij).left

variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {D : J ⥤ Over S}

/-- A cartesian étale system is pointwise étale, and every transition square is cartesian. -/
theorem CartesianEtaleSystem.spec (U : CartesianEtaleSystem D) :
    (∀ i, Etale (U.π.app i)) ∧
      ∀ {i j : J} (hij : i ⟶ j),
        IsPullback (U.functor.map hij) (U.π.app i) (U.π.app j) (D.map hij).left :=
  sorry

/-- The comparison morphism of pullbacks `X_i ×_X U ⟶ X_j ×_X U` along `hij : i ⟶ j`. -/
def etalePullbackMap (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left) {i j : J}
    (hij : i ⟶ j) :
    pullback (c.ι.app i).left f ⟶ pullback (c.ι.app j).left f :=
  pullback.map (c.ι.app i).left f (c.ι.app j).left f
    (D.map hij).left (𝟙 U) (𝟙 c.pt.left)
    ((Category.comp_id (c.ι.app i).left).trans
      (congrArg (fun φ : D.obj i ⟶ c.pt ↦ φ.left) (c.w hij).symm))
    ((Category.comp_id f).trans (Category.id_comp f).symm)

/-- The pullback comparison maps preserve identities. -/
theorem etalePullbackMap_id (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left) (i : J) :
    etalePullbackMap c f (𝟙 i) = 𝟙 (pullback (c.ι.app i).left f) :=
  sorry

/-- The pullback comparison maps preserve composition. -/
theorem etalePullbackMap_comp (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left)
    {i j k : J} (hij : i ⟶ j) (hjk : j ⟶ k) :
    etalePullbackMap c f (hij ≫ hjk) =
      etalePullbackMap c f hij ≫ etalePullbackMap c f hjk :=
  sorry

/-- The diagram `i ↦ X_i ×_X U` of pullbacks along a cocone. -/
def etalePullbackDiagram (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left) :
    J ⥤ Scheme.{u} where
  obj i := pullback (c.ι.app i).left f
  map hij := etalePullbackMap c f hij
  map_id i := etalePullbackMap_id c f i
  map_comp hij hjk := etalePullbackMap_comp c f hij hjk

/-- The object of `etalePullbackDiagram c f` at `i` is the pullback `X_i ×_X U`. -/
theorem etalePullbackDiagram_obj (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left) (i : J) :
    (etalePullbackDiagram c f).obj i = pullback (c.ι.app i).left f :=
  sorry

/-- The first projections of the pullback diagram are natural in the indexing morphisms. -/
theorem etalePullbackFst_naturality (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left)
    {i j : J} (hij : i ⟶ j) :
    etalePullbackMap c f hij ≫ pullback.fst (c.ι.app j).left f =
      pullback.fst (c.ι.app i).left f ≫ (D.map hij).left :=
  sorry

/-- The first projection from each pullback in an étale pullback diagram is étale. -/
theorem etalePullbackFst_etale (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left)
    (hf : Etale f) (i : J) :
    Etale (pullback.fst (c.ι.app i).left f) :=
  sorry

/-- Each transition square in an étale pullback diagram is a pullback square. -/
theorem etalePullbackMap_isPullback (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left)
    {i j : J} (hij : i ⟶ j) :
    IsPullback (etalePullbackMap c f hij) (pullback.fst (c.ι.app i).left f)
      (pullback.fst (c.ι.app j).left f) (D.map hij).left :=
  sorry

/-- The cartesian étale system obtained by pulling back an étale morphism `V ⟶ X` along the
cocone legs `X_i ⟶ X`. -/
def ofEtalePullback (c : Cocone D) (V : c.pt.left.Etale) : CartesianEtaleSystem D where
  functor := etalePullbackDiagram c V.hom
  π :=
    { app := fun i ↦ pullback.fst (c.ι.app i).left V.hom
      naturality := fun _ _ hij ↦ etalePullbackFst_naturality c V.hom hij }
  etale i := etalePullbackFst_etale c V.hom V.prop i
  isPullback hij := etalePullbackMap_isPullback c V.hom hij

/-- The underlying functor of `ofEtalePullback c V` is the pullback diagram along `V.hom`. -/
theorem ofEtalePullback_functor (c : Cocone D) (V : c.pt.left.Etale) :
    (ofEtalePullback c V).functor = etalePullbackDiagram c V.hom :=
  sorry

/-- The object of `ofEtalePullback c V` at `i` is the pullback `X_i ×_X V`. -/
theorem ofEtalePullback_obj (c : Cocone D) (V : c.pt.left.Etale) (i : J) :
    (ofEtalePullback c V).functor.obj i = pullback (c.ι.app i).left V.hom :=
  sorry

/-- The projection of `ofEtalePullback c V` at `i` is `pullback.fst`. -/
theorem ofEtalePullback_π (c : Cocone D) (V : c.pt.left.Etale) (i : J) :
    (ofEtalePullback c V).π.app i = pullback.fst (c.ι.app i).left V.hom :=
  sorry

/-- A cartesian étale system lies in the essential image of pullback from `X.Etale` when it is
isomorphic over `D` to `ofEtalePullback c V` for some `V : c.pt.left.Etale`. -/
def IsInEtaleEssImage (c : Cocone D) (U : CartesianEtaleSystem D) : Prop :=
  ∃ (V : c.pt.left.Etale) (e : U.functor ≅ (ofEtalePullback c V).functor),
    U.π = e.hom ≫ (ofEtalePullback c V).π

/-- Essential-image membership is an isomorphism over `D` with a pullback from `X.Etale`. -/
theorem isInEtaleEssImage_iff (c : Cocone D) (U : CartesianEtaleSystem D) :
    IsInEtaleEssImage c U ↔
      ∃ (V : c.pt.left.Etale) (e : U.functor ≅ (ofEtalePullback c V).functor),
        U.π = e.hom ≫ (ofEtalePullback c V).π :=
  sorry

/-- The second projections of the pullback diagram form a cocone. -/
theorem etalePullbackSnd_naturality (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left)
    {i j : J} (hij : i ⟶ j) :
    etalePullbackMap c f hij ≫ pullback.snd (c.ι.app j).left f =
      pullback.snd (c.ι.app i).left f :=
  sorry

/-- The cocone `U_i ⟶ U` with legs `pullback.snd : X_i ×_X U ⟶ U`. -/
def etalePullbackCocone (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left) :
    Cocone (etalePullbackDiagram c f) where
  pt := U
  ι :=
    { app := fun i ↦ pullback.snd (c.ι.app i).left f
      naturality := fun _ _ hij ↦ etalePullbackSnd_naturality c f hij }

/-- The apex of `etalePullbackCocone c f` is `U`. -/
theorem etalePullbackCocone_pt (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left) :
    (etalePullbackCocone c f).pt = U :=
  sorry

/-- The `i`-th leg of `etalePullbackCocone c f` is `pullback.snd`. -/
theorem etalePullbackCocone_ι (c : Cocone D) {U : Scheme.{u}} (f : U ⟶ c.pt.left) (i : J) :
    (etalePullbackCocone c f).ι.app i = pullback.snd (c.ι.app i).left f :=
  sorry

/-- The canonical morphism `∐ X_i ⟶ X` induced by a cocone in `Over S`. -/
def coproductToColimit [Small.{u} J] (c : Cocone D) :
    (∐ fun i : J ↦ (D.obj i).left) ⟶ c.pt.left :=
  Sigma.desc fun i ↦ (c.ι.app i).left

/-- Precomposition of `coproductToColimit c` with the `i`-th summand inclusion is the cocone
leg `X_i ⟶ X`. -/
theorem coproductToColimit_ι [Small.{u} J] (c : Cocone D) (i : J) :
    Sigma.ι (fun j : J ↦ (D.obj j).left) i ≫ coproductToColimit c = (c.ι.app i).left :=
  sorry

end AlgebraicGeometry.Scheme
