module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtalePullback

/-!
# Glueing modules on small étale sites of algebraic spaces

A sheaf of `𝒪_X`-modules on `X_étale` determines an `𝒪_U`-module on `U_étale` for every
object `U` of `X_étale`, together with module-pullback transition isomorphisms along
morphisms of `X_étale`. This module packages those compatible systems.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing
  (etale_siteHom idObj idObjHom ofOverMap_id ofOverMap_comp ofOverMap_triangle)
open CategoryTheory.Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing

variable {S : Scheme.{u}}

/-- The structure morphism of an object of `X_étale` is étale. -/
instance etale_objHom {X : AlgebraicSpace S} (U : smallEtaleSite X) : Etale U.hom :=
  U.prop

/-- Pullback of `𝒪`-modules along a morphism of `X_étale`, as module pullback of
`f_small`. -/
noncomputable def pullback {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    (ofOver U.left).Modules ⥤ (ofOver V.left).Modules :=
  Modules.pullback (ofOverMap f.left)

/-- Pullback of modules along a morphism of `X_étale` is module pullback of the induced
étale map of algebraic spaces. -/
theorem pullback_eq {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    pullback f = Modules.pullback (ofOverMap f.left) :=
  rfl

/-- The identification `𝒢|_{X_étale} ≅ f^* 𝒢` along a morphism of `X_étale`. -/
noncomputable def pullbackIsoRestrict {X : AlgebraicSpace S} {U V : smallEtaleSite X}
    (f : V ⟶ U) :
    pullback f ≅ Modules.restrictFunctor (ofOverMap f.left) :=
  (Modules.restrictFunctorIsoPullback (ofOverMap f.left)).symm

/-- The identity section maps for the restriction comparison are natural, additive,
scalar compatible, mutually inverse, and natural in the module sheaf. -/
private theorem restrictFunctorId_laws (Y : AlgebraicSpace S) :
    let F := Modules.restrictFunctor (𝟙 Y)
    let G := 𝟭 Y.Modules
    let R := structureSheaf Y
    let N : Prop := ∀ M : Y.Modules,
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (F.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (G.obj M)).obj.map a) ∧
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (G.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (F.obj M)).obj.map a)
    N ∧ ∀ n : N,
      let h (M : Y.Modules) :
          (ToInternal.underlying R).obj (F.obj M) ⟶
            (ToInternal.underlying R).obj (G.obj M) :=
        InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).1 }
      let i (M : Y.Modules) :
          (ToInternal.underlying R).obj (G.obj M) ⟶
            (ToInternal.underlying R).obj (F.obj M) :=
        InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).2 }
      let L : Prop := ∀ M : Y.Modules,
        (∀ A (x y : (F.obj M).val.obj A),
          underlyingApp R (h M) A (x + y) =
            underlyingApp R (h M) A x + underlyingApp R (h M) A y) ∧
        (∀ A (r : R.obj.obj A) (x : (F.obj M).val.obj A),
          underlyingApp R (h M) A (r • x) = r • underlyingApp R (h M) A x) ∧
        (∀ A (x y : (G.obj M).val.obj A),
          underlyingApp R (i M) A (x + y) =
            underlyingApp R (i M) A x + underlyingApp R (i M) A y) ∧
        (∀ A (r : R.obj.obj A) (x : (G.obj M).val.obj A),
          underlyingApp R (i M) A (r • x) = r • underlyingApp R (i M) A x)
      L ∧ ∀ l : L,
        let hom M := homOfUnderlying R (h M) (l M).1 (l M).2.1
        let inv M := homOfUnderlying R (i M) (l M).2.2.1 (l M).2.2.2
        (∀ M, (hom M ≫ inv M = 𝟙 (F.obj M)) ∧
          (inv M ≫ hom M = 𝟙 (G.obj M))) ∧
        (∀ {M M' : Y.Modules} (a : M ⟶ M'),
          F.map a ≫ hom M' = hom M ≫ G.map a) :=
  sorry

set_option maxHeartbeats 800000 in
/-- Restriction of modules along an identity morphism is canonically the identity. -/
noncomputable def restrictFunctorId (Y : AlgebraicSpace S) :
    Modules.restrictFunctor (𝟙 Y) ≅ 𝟭 Y.Modules := by
  let F := Modules.restrictFunctor (𝟙 Y)
  let G := 𝟭 Y.Modules
  let R := structureSheaf Y
  have n : ∀ M : Y.Modules,
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (F.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (G.obj M)).obj.map a) ∧
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (G.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (F.obj M)).obj.map a) := (by exact (restrictFunctorId_laws Y).1)
  let h (M : Y.Modules) :
      (ToInternal.underlying R).obj (F.obj M) ⟶
        (ToInternal.underlying R).obj (G.obj M) :=
    InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).1 }
  let i (M : Y.Modules) :
      (ToInternal.underlying R).obj (G.obj M) ⟶
        (ToInternal.underlying R).obj (F.obj M) :=
    InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).2 }
  have l : ∀ M : Y.Modules,
      (∀ A (x y : (F.obj M).val.obj A),
        underlyingApp R (h M) A (x + y) =
          underlyingApp R (h M) A x + underlyingApp R (h M) A y) ∧
      (∀ A (r : R.obj.obj A) (x : (F.obj M).val.obj A),
        underlyingApp R (h M) A (r • x) = r • underlyingApp R (h M) A x) ∧
      (∀ A (x y : (G.obj M).val.obj A),
        underlyingApp R (i M) A (x + y) =
          underlyingApp R (i M) A x + underlyingApp R (i M) A y) ∧
      (∀ A (r : R.obj.obj A) (x : (G.obj M).val.obj A),
        underlyingApp R (i M) A (r • x) = r • underlyingApp R (i M) A x) := (by exact ((restrictFunctorId_laws Y).2 n).1)
  exact NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying R (h M) (l M).1 (l M).2.1
        inv := homOfUnderlying R (i M) (l M).2.2.1 (l M).2.2.2
        hom_inv_id := by exact ((((restrictFunctorId_laws Y).2 n).2 l).1 M).1
        inv_hom_id := by exact ((((restrictFunctorId_laws Y).2 n).2 l).1 M).2 })
    (by intro M M' a; exact (((restrictFunctorId_laws Y).2 n).2 l).2 a)

/-- Pullback of modules along an identity morphism is canonically the identity. -/
noncomputable def modulesPullbackId (Y : AlgebraicSpace S) :
    Modules.pullback (𝟙 Y) ≅ 𝟭 Y.Modules :=
  (Modules.restrictFunctorIsoPullback (𝟙 Y)).symm ≪≫ restrictFunctorId Y

/-- Pullback along an identity is canonically isomorphic to the identity on small étale
modules. -/
noncomputable def pullbackId {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    pullback (𝟙 U) ≅ 𝟭 (ofOver U.left).Modules :=
  eqToIso (congrArg (fun h ↦ Modules.pullback h) (ofOverMap_id U.left)) ≪≫
    modulesPullbackId (ofOver U.left)

set_option maxHeartbeats 800000 in
/-- The identity section maps for the restriction comparison are natural, additive,
scalar compatible, mutually inverse, and natural in the module sheaf. -/
private theorem restrictFunctorComp_laws {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (g : Y ⟶ Z) [Etale g] :
    let F := Modules.restrictFunctor g ⋙ Modules.restrictFunctor f
    let G := Modules.restrictFunctor (f ≫ g)
    let R := structureSheaf X
    let N : Prop := ∀ M : Z.Modules,
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (F.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (G.obj M)).obj.map a) ∧
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (G.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (F.obj M)).obj.map a)
    N ∧ ∀ n : N,
      let h (M : Z.Modules) :
          (ToInternal.underlying R).obj (F.obj M) ⟶
            (ToInternal.underlying R).obj (G.obj M) :=
        InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).1 }
      let i (M : Z.Modules) :
          (ToInternal.underlying R).obj (G.obj M) ⟶
            (ToInternal.underlying R).obj (F.obj M) :=
        InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).2 }
      let L : Prop := ∀ M : Z.Modules,
        (∀ A (x y : (F.obj M).val.obj A),
          underlyingApp R (h M) A (x + y) =
            underlyingApp R (h M) A x + underlyingApp R (h M) A y) ∧
        (∀ A (r : R.obj.obj A) (x : (F.obj M).val.obj A),
          underlyingApp R (h M) A (r • x) = r • underlyingApp R (h M) A x) ∧
        (∀ A (x y : (G.obj M).val.obj A),
          underlyingApp R (i M) A (x + y) =
            underlyingApp R (i M) A x + underlyingApp R (i M) A y) ∧
        (∀ A (r : R.obj.obj A) (x : (G.obj M).val.obj A),
          underlyingApp R (i M) A (r • x) = r • underlyingApp R (i M) A x)
      L ∧ ∀ l : L,
        let hom M := homOfUnderlying R (h M) (l M).1 (l M).2.1
        let inv M := homOfUnderlying R (i M) (l M).2.2.1 (l M).2.2.2
        (∀ M, (hom M ≫ inv M = 𝟙 (F.obj M)) ∧
          (inv M ≫ hom M = 𝟙 (G.obj M))) ∧
        (∀ {M M' : Z.Modules} (a : M ⟶ M'),
          F.map a ≫ hom M' = hom M ≫ G.map a) :=
  sorry

set_option maxHeartbeats 800000 in
/-- Restriction of modules along an étale composite is the composite of the restrictions. -/
noncomputable def restrictFunctorComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (g : Y ⟶ Z) [Etale g] :
    Modules.restrictFunctor g ⋙ Modules.restrictFunctor f ≅ Modules.restrictFunctor (f ≫ g) := by
  let F := Modules.restrictFunctor g ⋙ Modules.restrictFunctor f
  let G := Modules.restrictFunctor (f ≫ g)
  let R := structureSheaf X
  have n : ∀ M : Z.Modules,
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (F.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (G.obj M)).obj.map a) ∧
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (G.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (F.obj M)).obj.map a) := (by exact (restrictFunctorComp_laws f g).1)
  let h (M : Z.Modules) :
      (ToInternal.underlying R).obj (F.obj M) ⟶
        (ToInternal.underlying R).obj (G.obj M) :=
    InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).1 }
  let i (M : Z.Modules) :
      (ToInternal.underlying R).obj (G.obj M) ⟶
        (ToInternal.underlying R).obj (F.obj M) :=
    InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).2 }
  have l : ∀ M : Z.Modules,
      (∀ A (x y : (F.obj M).val.obj A),
        underlyingApp R (h M) A (x + y) =
          underlyingApp R (h M) A x + underlyingApp R (h M) A y) ∧
      (∀ A (r : R.obj.obj A) (x : (F.obj M).val.obj A),
        underlyingApp R (h M) A (r • x) = r • underlyingApp R (h M) A x) ∧
      (∀ A (x y : (G.obj M).val.obj A),
        underlyingApp R (i M) A (x + y) =
          underlyingApp R (i M) A x + underlyingApp R (i M) A y) ∧
      (∀ A (r : R.obj.obj A) (x : (G.obj M).val.obj A),
        underlyingApp R (i M) A (r • x) = r • underlyingApp R (i M) A x) := (by exact ((restrictFunctorComp_laws f g).2 n).1)
  exact NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying R (h M) (l M).1 (l M).2.1
        inv := homOfUnderlying R (i M) (l M).2.2.1 (l M).2.2.2
        hom_inv_id := by exact ((((restrictFunctorComp_laws f g).2 n).2 l).1 M).1
        inv_hom_id := by exact ((((restrictFunctorComp_laws f g).2 n).2 l).1 M).2 })
    (by intro M M' a; exact (((restrictFunctorComp_laws f g).2 n).2 l).2 a)

/-- Successive pullbacks of modules along étale morphisms identify with pullback along the
composite. -/
noncomputable def modulesPullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (g : Y ⟶ Z) [Etale g] :
    Modules.pullback g ⋙ Modules.pullback f ≅ Modules.pullback (f ≫ g) :=
  Functor.isoWhiskerRight (Modules.restrictFunctorIsoPullback g).symm (Modules.pullback f) ≪≫
    Functor.isoWhiskerLeft (Modules.restrictFunctor g)
      (Modules.restrictFunctorIsoPullback f).symm ≪≫
    restrictFunctorComp f g ≪≫ Modules.restrictFunctorIsoPullback (f ≫ g)

/-- Successive pullbacks of small étale modules are canonically isomorphic to pullback along
the composite. -/
noncomputable def pullbackComp {X : AlgebraicSpace S} {U V W : smallEtaleSite X}
    (f : V ⟶ U) (g : W ⟶ V) :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  modulesPullbackComp (ofOverMap g.left) (ofOverMap f.left) ≪≫
    eqToIso (congrArg (fun h ↦ Modules.pullback h) (ofOverMap_comp f.left g.left).symm)

/-- A compatible system of modules on the small étale sites of schemes étale over an
algebraic space. -/
structure Object {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The sheaf of `𝒪_U`-modules on the small étale site of a scheme étale over `X`. -/
  obj (U : smallEtaleSite X) : (ofOver U.left).Modules
  /-- The module-pullback transition isomorphism `c_f : f_small^* F_U ≅ F_{U'}`. -/
  transition {U V : smallEtaleSite X} (f : V ⟶ U) : (pullback f).obj (obj U) ≅ obj V
  /-- The transition along an identity is the canonical identity comparison. -/
  transition_id (U : smallEtaleSite X) :
    transition (𝟙 U) = (pullbackId U).app (obj U)
  /-- The transitions satisfy the module-pullback cocycle
  `c_g ∘ g_small^* c_f = c_{f ∘ g}`. -/
  transition_comp {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V) :
    (pullbackComp f g).app (obj U) ≪≫ transition (g ≫ f) =
      (pullback g).mapIso (transition f) ≪≫ transition g

namespace Object

variable {X : AlgebraicSpace S}

/-- Invertible module-pullback transitions satisfying the composition cocycle agree
with the canonical identity comparison on identity morphisms. -/
theorem transition_id_of_comp
    (obj : ∀ U : smallEtaleSite X, (ofOver U.left).Modules)
    (transition : ∀ {U V : smallEtaleSite X} (f : V ⟶ U),
      (pullback f).obj (obj U) ≅ obj V)
    (transition_comp : ∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
      (pullbackComp f g).app (obj U) ≪≫ transition (g ≫ f) =
        (pullback g).mapIso (transition f) ≪≫ transition g) :
    ∀ U : smallEtaleSite X, transition (𝟙 U) = (pullbackId U).app (obj U) :=
  sorry

/-- A family of module sheaves with invertible transitions satisfying the composition
cocycle determines a compatible system, with its identity law derived from the cocycle. -/
noncomputable def ofCocycle
    (obj : ∀ U : smallEtaleSite X, (ofOver U.left).Modules)
    (transition : ∀ {U V : smallEtaleSite X} (f : V ⟶ U),
      (pullback f).obj (obj U) ≅ obj V)
    (transition_comp : ∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
      (pullbackComp f g).app (obj U) ≪≫ transition (g ≫ f) =
        (pullback g).mapIso (transition f) ≪≫ transition g) : Object X where
  obj := obj
  transition := transition
  transition_id := transition_id_of_comp obj transition transition_comp
  transition_comp := transition_comp

/-- The fields of a compatible small-étale module system express identity and the cocycle
condition for its transition isomorphisms. -/
theorem spec (F : Object X) :
    (∀ U : smallEtaleSite X, F.transition (𝟙 U) = (pullbackId U).app (F.obj U)) ∧
      (∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
        (pullbackComp f g).app (F.obj U) ≪≫ F.transition (g ≫ f) =
          (pullback g).mapIso (F.transition f) ≪≫ F.transition g) :=
  sorry

end Object

/-- A morphism of compatible small-étale module systems is a componentwise module morphism
commuting with every transition isomorphism. -/
@[ext]
structure Hom {X : AlgebraicSpace S} (F G : Object X) where
  /-- The component over an object of `X_étale`. -/
  app (U : smallEtaleSite X) : F.obj U ⟶ G.obj U
  /-- Component maps commute with module-pullback transitions. -/
  naturality {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map (app U)) (F.transition f).hom (G.transition f).hom (app V)

namespace Hom

variable {X : AlgebraicSpace S}

/-- Identity component maps commute with the transition isomorphisms. -/
private theorem id_naturality (F : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map (𝟙 (F.obj U))) (F.transition f).hom
      (F.transition f).hom (𝟙 (F.obj V)) :=
  sorry

/-- The identity compatible morphism. -/
def id (F : Object X) : Hom F F where
  app U := 𝟙 (F.obj U)
  naturality := by exact id_naturality F

/-- Composites of compatible component maps commute with the transitions. -/
private theorem comp_naturality {F G H : Object X} (α : Hom F G) (β : Hom G H)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map (α.app U ≫ β.app U)) (F.transition f).hom
      (H.transition f).hom (α.app V ≫ β.app V) :=
  sorry

/-- Composition of compatible morphisms. -/
def comp {F G H : Object X} (α : Hom F G) (β : Hom G H) : Hom F H where
  app U := α.app U ≫ β.app U
  naturality := by exact comp_naturality α β

/-- Composing a compatible morphism with the identity on its source leaves it unchanged. -/
theorem id_comp {F G : Object X} (α : Hom F G) : comp (id F) α = α :=
  sorry

/-- Composing a compatible morphism with the identity on its target leaves it unchanged. -/
theorem comp_id {F G : Object X} (α : Hom F G) : comp α (id G) = α :=
  sorry

/-- Componentwise composition of compatible module-system morphisms is associative. -/
theorem assoc {F G H K : Object X} (α : Hom F G) (β : Hom G H) (γ : Hom H K) :
    comp (comp α β) γ = comp α (comp β γ) :=
  sorry

end Hom

/-- The category of compatible module systems, bundled without installing a global category
instance on the explicit object structure. -/
noncomputable def category (X : AlgebraicSpace S) : Cat :=
  { α := Object X
    str :=
      { Hom := Hom
        id := Hom.id
        comp := Hom.comp
        id_comp := Hom.id_comp
        comp_id := Hom.comp_id
        assoc := Hom.assoc } }

/-- Restriction of modules along the structure morphism of an object of `X_étale`. -/
noncomputable def restrictFunctor_hom {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    X.Modules ⥤ (ofOver U.left).Modules :=
  @Modules.restrictFunctor _ _ _ U.hom U.prop

/-- Identification of restriction along a structure morphism with module pullback. -/
noncomputable def restrictFunctorIsoPullback_hom {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    restrictFunctor_hom U ≅ Modules.pullback U.hom :=
  @Modules.restrictFunctorIsoPullback _ _ _ U.hom U.prop

/-- The sheaf of modules on `U_étale` obtained by module pullback along the structure morphism
of `U`. -/
noncomputable def fromModulesObj {X : AlgebraicSpace S} (F : X.Modules) (U : smallEtaleSite X) :
    (ofOver U.left).Modules :=
  (Modules.pullback U.hom).obj F

set_option maxHeartbeats 800000 in
/-- The identity section maps for the restriction comparison are natural, additive,
scalar compatible, mutually inverse, and natural in the module sheaf. -/
private theorem restrictFunctorComp_hom_laws {X : AlgebraicSpace S} {U V : smallEtaleSite X}
    (f : V ⟶ U) :
    let F := restrictFunctor_hom U ⋙ Modules.restrictFunctor (ofOverMap f.left)
    let G := @Modules.restrictFunctor _ _ _ (ofOverMap f.left ≫ U.hom)
        (@Etale.etale_comp _ _ _ (ofOverMap f.left) _ U.hom (etale_siteHom f) U.prop)
    let R := structureSheaf (ofOver V.left)
    let N : Prop := ∀ M : X.Modules,
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (F.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (G.obj M)).obj.map a) ∧
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (G.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (F.obj M)).obj.map a)
    N ∧ ∀ n : N,
      let h (M : X.Modules) :
          (ToInternal.underlying R).obj (F.obj M) ⟶
            (ToInternal.underlying R).obj (G.obj M) :=
        InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).1 }
      let i (M : X.Modules) :
          (ToInternal.underlying R).obj (G.obj M) ⟶
            (ToInternal.underlying R).obj (F.obj M) :=
        InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).2 }
      let L : Prop := ∀ M : X.Modules,
        (∀ A (x y : (F.obj M).val.obj A),
          underlyingApp R (h M) A (x + y) =
            underlyingApp R (h M) A x + underlyingApp R (h M) A y) ∧
        (∀ A (r : R.obj.obj A) (x : (F.obj M).val.obj A),
          underlyingApp R (h M) A (r • x) = r • underlyingApp R (h M) A x) ∧
        (∀ A (x y : (G.obj M).val.obj A),
          underlyingApp R (i M) A (x + y) =
            underlyingApp R (i M) A x + underlyingApp R (i M) A y) ∧
        (∀ A (r : R.obj.obj A) (x : (G.obj M).val.obj A),
          underlyingApp R (i M) A (r • x) = r • underlyingApp R (i M) A x)
      L ∧ ∀ l : L,
        let hom M := homOfUnderlying R (h M) (l M).1 (l M).2.1
        let inv M := homOfUnderlying R (i M) (l M).2.2.1 (l M).2.2.2
        (∀ M, (hom M ≫ inv M = 𝟙 (F.obj M)) ∧
          (inv M ≫ hom M = 𝟙 (G.obj M))) ∧
        (∀ {M M' : X.Modules} (a : M ⟶ M'),
          F.map a ≫ hom M' = hom M ≫ G.map a) :=
  sorry

set_option maxHeartbeats 800000 in
/-- Restriction along a morphism of `X_étale` then along a structure morphism identifies with
restriction along the triangle composite. -/
noncomputable def restrictFunctorComp_hom {X : AlgebraicSpace S} {U V : smallEtaleSite X}
    (f : V ⟶ U) :
    restrictFunctor_hom U ⋙ Modules.restrictFunctor (ofOverMap f.left) ≅ @Modules.restrictFunctor _ _ _ (ofOverMap f.left ≫ U.hom)
        (@Etale.etale_comp _ _ _ (ofOverMap f.left) _ U.hom (etale_siteHom f) U.prop) := by
  let F := restrictFunctor_hom U ⋙ Modules.restrictFunctor (ofOverMap f.left)
  let G := @Modules.restrictFunctor _ _ _ (ofOverMap f.left ≫ U.hom)
        (@Etale.etale_comp _ _ _ (ofOverMap f.left) _ U.hom (etale_siteHom f) U.prop)
  let R := structureSheaf (ofOver V.left)
  have n : ∀ M : X.Modules,
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (F.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (G.obj M)).obj.map a) ∧
      (∀ A B (a : A ⟶ B),
        ((ToInternal.underlying R).obj (G.obj M)).obj.map a ≫ 𝟙 _ =
          𝟙 _ ≫ ((ToInternal.underlying R).obj (F.obj M)).obj.map a) := (by exact (restrictFunctorComp_hom_laws f).1)
  let h (M : X.Modules) :
      (ToInternal.underlying R).obj (F.obj M) ⟶
        (ToInternal.underlying R).obj (G.obj M) :=
    InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).1 }
  let i (M : X.Modules) :
      (ToInternal.underlying R).obj (G.obj M) ⟶
        (ToInternal.underlying R).obj (F.obj M) :=
    InducedCategory.homMk { app := fun _ ↦ 𝟙 _, naturality := (n M).2 }
  have l : ∀ M : X.Modules,
      (∀ A (x y : (F.obj M).val.obj A),
        underlyingApp R (h M) A (x + y) =
          underlyingApp R (h M) A x + underlyingApp R (h M) A y) ∧
      (∀ A (r : R.obj.obj A) (x : (F.obj M).val.obj A),
        underlyingApp R (h M) A (r • x) = r • underlyingApp R (h M) A x) ∧
      (∀ A (x y : (G.obj M).val.obj A),
        underlyingApp R (i M) A (x + y) =
          underlyingApp R (i M) A x + underlyingApp R (i M) A y) ∧
      (∀ A (r : R.obj.obj A) (x : (G.obj M).val.obj A),
        underlyingApp R (i M) A (r • x) = r • underlyingApp R (i M) A x) := (by exact ((restrictFunctorComp_hom_laws f).2 n).1)
  exact NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying R (h M) (l M).1 (l M).2.1
        inv := homOfUnderlying R (i M) (l M).2.2.1 (l M).2.2.2
        hom_inv_id := by exact ((((restrictFunctorComp_hom_laws f).2 n).2 l).1 M).1
        inv_hom_id := by exact ((((restrictFunctorComp_hom_laws f).2 n).2 l).1 M).2 })
    (by intro M M' a; exact (((restrictFunctorComp_hom_laws f).2 n).2 l).2 a)

/-- Successive pullbacks along a morphism of `X_étale` and a structure morphism identify with
pullback along the triangle composite. -/
noncomputable def modulesPullbackComp_hom {X : AlgebraicSpace S} {U V : smallEtaleSite X}
    (f : V ⟶ U) :
    Modules.pullback U.hom ⋙ Modules.pullback (ofOverMap f.left) ≅
      Modules.pullback (ofOverMap f.left ≫ U.hom) :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback_hom U).symm
      (Modules.pullback (ofOverMap f.left)) ≪≫
    Functor.isoWhiskerLeft (restrictFunctor_hom U)
      (Modules.restrictFunctorIsoPullback (ofOverMap f.left)).symm ≪≫
    restrictFunctorComp_hom f ≪≫
      @Modules.restrictFunctorIsoPullback _ _ _ (ofOverMap f.left ≫ U.hom)
        (@Etale.etale_comp _ _ _ (ofOverMap f.left) _ U.hom (etale_siteHom f) U.prop)

/-- The canonical transition of the compatible system associated to a sheaf of modules on
`X_étale`. -/
noncomputable def fromModulesTransition {X : AlgebraicSpace S} (F : X.Modules)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    (pullback f).obj (fromModulesObj F U) ≅ fromModulesObj F V :=
  (modulesPullbackComp_hom f).app F ≪≫
    eqToIso (congrArg (fun h ↦ (Modules.pullback h).obj F) (ofOverMap_triangle f))

namespace Object

variable {X : AlgebraicSpace S}

/-- The canonical pullback transitions satisfy identity normalization and the composition
cocycle. -/
private theorem ofModules_laws (F : X.Modules) :
    (∀ U : smallEtaleSite X,
      fromModulesTransition F (𝟙 U) = (pullbackId U).app (fromModulesObj F U)) ∧
    (∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
      (pullbackComp f g).app (fromModulesObj F U) ≪≫ fromModulesTransition F (g ≫ f) =
        (pullback g).mapIso (fromModulesTransition F f) ≪≫ fromModulesTransition F g) :=
  sorry

/-- The compatible system of small étale modules obtained by module pullback from a sheaf of
modules on `X_étale`. -/
noncomputable def ofModules (F : X.Modules) : Object X where
  obj := fromModulesObj F
  transition := fromModulesTransition F
  transition_id := by exact (ofModules_laws F).1
  transition_comp := by exact (ofModules_laws F).2

end Object

/-- Pullback of a module morphism commutes with the canonical chart transitions. -/
private theorem fromModulesMap_naturality {X : AlgebraicSpace S} {F G : X.Modules}
    (η : F ⟶ G) {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map ((Modules.pullback U.hom).map η))
      (fromModulesTransition F f).hom (fromModulesTransition G f).hom
      ((Modules.pullback V.hom).map η) :=
  sorry

/-- A morphism of modules on `X_étale` induces the componentwise compatible morphism
between their pullback systems. -/
noncomputable def fromModulesMap {X : AlgebraicSpace S} {F G : X.Modules} (η : F ⟶ G) :
    Hom (Object.ofModules F) (Object.ofModules G) where
  app U := (Modules.pullback U.hom).map η
  naturality := by exact fromModulesMap_naturality η

/-- Pullback of module morphisms to compatible systems preserves identities and composition. -/
private theorem fromModules_laws (X : AlgebraicSpace S) :
    (∀ F : X.Modules, fromModulesMap (𝟙 F) = Hom.id (Object.ofModules F)) ∧
    (∀ {F G H : X.Modules} (α : F ⟶ G) (β : G ⟶ H),
      fromModulesMap (α ≫ β) = Hom.comp (fromModulesMap α) (fromModulesMap β)) :=
  sorry

/-- Module pullback of sheaves of modules on `X_étale` to compatible systems on all
`U_étale`. -/
noncomputable def fromModules (X : AlgebraicSpace S) :
    X.Modules ⥤ category X where
  obj := Object.ofModules
  map := fromModulesMap
  map_id := by exact (fromModules_laws X).1
  map_comp := by exact (fromModules_laws X).2

variable {X : AlgebraicSpace S}

/-- The object of the compatible system associated to a sheaf of modules is pullback along
the structure morphism. -/
theorem fromModules_obj (F : X.Modules) (U : smallEtaleSite X) :
    ((fromModules X).obj F).obj U = (Modules.pullback U.hom).obj F :=
  rfl

/-- The transition of the compatible system associated to a sheaf of modules is the
functoriality isomorphism of module pullback. -/
theorem fromModules_transition (F : X.Modules) {U V : smallEtaleSite X} (f : V ⟶ U) :
    ((fromModules X).obj F).transition f = fromModulesTransition F f :=
  rfl

/-- Sections of a compatible system at an object of `X_étale`, as the module of `F_U` at the
identity object of `U_étale`. -/
noncomputable def toModulesObj (G : Object X) (U : smallEtaleSite X) :
    ModuleCat ((structureSheaf X).obj.obj (op U)) :=
  (G.obj U).val.obj (op (idObj U.left))

/-- The underlying function of reconstructed restriction along a morphism of `X_étale`. -/
noncomputable def toModulesMapType (G : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    ((G.obj U).val.obj (op (idObj U.left)) : Type u) ⟶
      ((G.obj V).val.obj (op (idObj V.left)) : Type u) :=
  ToInternal.restrictionApp (structureSheaf (ofOver U.left)) (G.obj U) (idObjHom f).op ≫
    ((Modules.pullbackIsoInverseImage (ofOverMap f.left)).inv.app (G.obj U)).hom.app
      (op (idObj V.left)) ≫
    ToInternal.carrierMapApp (structureSheaf (ofOver V.left)) (G.transition f).hom
      (op (idObj V.left))

/-- The reconstructed restriction function preserves addition and the restricted scalar
multiplication. -/
private theorem toModulesMapLinear_laws (G : Object X) {U V : smallEtaleSite X}
    (f : V ⟶ U) :
    (∀ x y : toModulesObj G U,
      toModulesMapType G f (x + y) = toModulesMapType G f x + toModulesMapType G f y) ∧
    (∀ (r : (structureSheaf X).obj.obj (op U)) (x : toModulesObj G U),
      toModulesMapType G f (r • x) =
        @SMul.smul _ _
          ((ModuleCat.restrictScalars ((structureSheaf X).obj.map f.op).hom).obj
            (toModulesObj G V)).isModule.toSMul r (toModulesMapType G f x)) :=
  sorry

set_option maxRecDepth 2048 in
/-- Linearity of reconstructed restriction along a morphism of `X_étale`. -/
noncomputable def toModulesMapLinear (G : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    (toModulesObj G U : Type u) →ₗ[(structureSheaf X).obj.obj (op U)]
      ((ModuleCat.restrictScalars ((structureSheaf X).obj.map f.op).hom).obj
        (toModulesObj G V) : Type u) where
  toFun := toModulesMapType G f
  map_add' := by exact (toModulesMapLinear_laws G f).1
  map_smul' r x := by exact (toModulesMapLinear_laws G f).2 r x

/-- Restriction of reconstructed modules along a morphism of `X_étale`. -/
noncomputable def toModulesMap (G : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    toModulesObj G U ⟶
      (ModuleCat.restrictScalars ((structureSheaf X).obj.map f.op).hom).obj (toModulesObj G V) :=
  ConcreteCategory.ofHom (toModulesMapLinear G f)

/-- Reconstructed restriction maps satisfy the identity and composition laws for a
presheaf of modules over the structure sheaf. -/
private theorem toModulesPresheaf_laws (G : Object X) :
    (∀ U : (smallEtaleSite X)ᵒᵖ,
      toModulesMap G (𝟙 U).unop =
        (ModuleCat.restrictScalarsId' ((structureSheaf X).obj.map (𝟙 U)).hom
          (congrArg RingCat.Hom.hom ((structureSheaf X).obj.map_id U))).inv.app
            (toModulesObj G U.unop)) ∧
    (∀ {U V W : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W),
      toModulesMap G (f ≫ g).unop =
        toModulesMap G f.unop ≫ (ModuleCat.restrictScalars _).map (toModulesMap G g.unop) ≫
          (ModuleCat.restrictScalarsComp' ((structureSheaf X).obj.map f).hom
            ((structureSheaf X).obj.map g).hom ((structureSheaf X).obj.map (f ≫ g)).hom
            (congrArg RingCat.Hom.hom ((structureSheaf X).obj.map_comp f g))).inv.app
              (toModulesObj G W.unop)) :=
  sorry

/-- The presheaf of modules on `X_étale` reconstructed from identity-object sections of a
compatible system. -/
noncomputable def toModulesPresheaf (G : Object X) :
    PresheafOfModules (structureSheaf X).obj where
  obj U := toModulesObj G U.unop
  map f := toModulesMap G f.unop
  map_id := by exact (toModulesPresheaf_laws G).1
  map_comp := by exact (toModulesPresheaf_laws G).2

/-- The reconstructed presheaf of a compatible module system is a sheaf on `X_étale`. -/
theorem toModules_isSheaf (G : Object X) :
    Presheaf.IsSheaf (smallEtaleTopology X) (toModulesPresheaf G).presheaf :=
  sorry

/-- Evaluation of compatible component morphisms at identity charts is natural with
respect to reconstructed restrictions and preserves identities and composition. -/
private theorem toModules_laws (X : AlgebraicSpace S) :
    let obj (G : Object X) : X.Modules := ⟨toModulesPresheaf G, toModules_isSheaf G⟩
    let N : Prop := ∀ {G H : Object X} (α : Hom G H)
      {U V : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V),
      (toModulesPresheaf G).map f ≫ (ModuleCat.restrictScalars _).map
        ((α.app V.unop).val.app (op (idObj V.unop.left))) =
      (α.app U.unop).val.app (op (idObj U.unop.left)) ≫ (toModulesPresheaf H).map f
    N ∧ ∀ n : N,
      let map {G H : Object X} (α : Hom G H) : obj G ⟶ obj H :=
        { val := { app := fun U ↦ (α.app U.unop).val.app (op (idObj U.unop.left))
                   naturality := n α } }
      (∀ G : Object X, map (Hom.id G) = 𝟙 (obj G)) ∧
      (∀ {G H K : Object X} (α : Hom G H) (β : Hom H K),
        map (Hom.comp α β) = map α ≫ map β) :=
  sorry

/-- Reconstruction of a sheaf of modules on `X_étale` from a compatible system of modules on
all `U_étale`. -/
noncomputable def toModules (X : AlgebraicSpace S) :
    category X ⥤ X.Modules where
  obj G := ⟨toModulesPresheaf G, toModules_isSheaf G⟩
  map {G H} α :=
    { val :=
        { app := fun U ↦ (α.app U.unop).val.app (op (idObj U.unop.left))
          naturality := by exact (toModules_laws X).1 α } }
  map_id := by exact ((toModules_laws X).2 (toModules_laws X).1).1
  map_comp := by exact ((toModules_laws X).2 (toModules_laws X).1).2

/-- Reconstructed sections of a compatible module system at `U` are the sections of `F_U` at
the identity object of `U_étale`. -/
theorem toModules_obj (G : Object X) (U : smallEtaleSite X) :
    (((toModules X).obj G).val.obj (op U)) = (G.obj U).val.obj (op (idObj U.left)) :=
  rfl

/-- Module pullback from sheaves of modules on `X_étale` to compatible systems on all small
étale sites is an equivalence of categories. -/
instance fromModules_isEquivalence (X : AlgebraicSpace S) :
    (fromModules X).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing
