/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import stacks_project.Chap78.Definition_78_9_3_Torsor
public import stacks_project.Chap95.Lemma_95_14_10_Torsors

/-!
# Descent data for principal homogeneous spaces

Chosen fibre-product descent data for principal homogeneous `H_{U_i}`-spaces
along an fppf covering of a scheme, including the canonical datum of a global
principal homogeneous space.

The comparison maps are the Chap80 overlap/restriction API, rebuilt on the
`pullbackAction` owner from Lemma 95.14.10 so they can be imported together
with `Principal.forget`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open GroupAlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupAlgebraicSpace.Principal

/-- Comparison of group objects `G_{B''}` obtained by pulling back along a
composite versus pulling back in stages. -/
def grpOverPullbackCompIso {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (G : GroupAlgebraicSpace B) :
    grpOverPullback G (g ≫ f) ≅ grpOverPullback (grpOverPullback G f) g :=
  Grp.mkIso ((Over.pullbackComp g f).app G.X) sorry sorry

/-- Transport of a `G`-action along an isomorphism of group algebraic spaces
over the same base, by restriction of scalars along the inverse. -/
def actionCongr {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G G' : GroupAlgebraicSpace B} (e : G ≅ G') (X : Action G) : Action G' :=
  (CategoryTheory.Mod.comap e.inv.hom.hom).obj X

variable {U : Scheme.{u}}

/-- The structure morphism `V ⟶ U` as a morphism of schemes over `U`. -/
def overToBase (V : Over U) : V ⟶ Over.mk (𝟙 U) :=
  Over.homMk V.hom (Category.comp_id V.hom)

/-- Morphisms to `Over.mk (𝟙 U)` are unique. -/
theorem overToBase_unique (V : Over U) (f : V ⟶ Over.mk (𝟙 U)) :
    f = overToBase V := sorry

/-- The morphism `U_i ⟶ U` of algebraic spaces over `U`. -/
def base (V : Over U) : ofOver V ⟶ ofOver (Over.mk (𝟙 U)) :=
  ofOverMap (overToBase V)

/-- Pulling `U_i ⟶ U` back along `W ⟶ U_i` recovers `W ⟶ U`. -/
theorem base_comp {V W : Over U} (f : W ⟶ V) :
    ofOverMap f ≫ base V = base W := sorry

variable {I : Type v} (Ui : I → Over U)
variable (H : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 U))))

/-- The fibre product `U_i ×_U U_j` as a scheme over `U`. -/
def pair (i j : I) : Over U :=
  Over.mk (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom)

/-- Compatibility of `pr1` with the structure morphisms to `U`. -/
theorem pr1_w (i j : I) :
    pullback.snd (Ui i).hom (Ui j).hom ≫ (Ui j).hom = (pair Ui i j).hom := sorry

/-- The projection `pr₀ : U_i ×_U U_j ⟶ U_i`. -/
def pr0 (i j : I) : pair Ui i j ⟶ Ui i :=
  Over.homMk (pullback.fst (Ui i).hom (Ui j).hom) rfl

/-- The projection `pr₁ : U_i ×_U U_j ⟶ U_j`. -/
def pr1 (i j : I) : pair Ui i j ⟶ Ui j :=
  Over.homMk (pullback.snd (Ui i).hom (Ui j).hom) (pr1_w Ui i j)

/-- The triple fibre product `U_i ×_U U_j ×_U U_k` as
`(U_i ×_U U_j) ×_U U_k` over `U`. -/
def triple (i j k : I) : Over U :=
  Over.mk
    (pullback.fst (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom) (Ui k).hom ≫
      (pair Ui i j).hom)

/-- The projection `pr₀₁ : U_i ×_U U_j ×_U U_k ⟶ U_i ×_U U_j`. -/
def pr01 (i j k : I) : triple Ui i j k ⟶ pair Ui i j :=
  Over.homMk
    (pullback.fst (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom) (Ui k).hom) rfl

/-- The two legs of `pr12Scheme` agree over `U`. -/
theorem pr12Scheme_w (i j k : I) :
    (pullback.fst (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom) (Ui k).hom ≫
        pullback.snd (Ui i).hom (Ui j).hom) ≫
        (Ui j).hom =
      pullback.snd (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom)
          (Ui k).hom ≫
        (Ui k).hom := sorry

/-- Underlying scheme map of `pr₁₂`. -/
def pr12Scheme (i j k : I) : (triple Ui i j k).left ⟶ (pair Ui j k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom) (Ui k).hom ≫
      pullback.snd (Ui i).hom (Ui j).hom)
    (pullback.snd (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom) (Ui k).hom)
    (pr12Scheme_w Ui i j k)

/-- `pr12Scheme` lies over `U`. -/
theorem pr12_w (i j k : I) :
    pr12Scheme Ui i j k ≫ (pair Ui j k).hom = (triple Ui i j k).hom := sorry

/-- The projection `pr₁₂ : U_i ×_U U_j ×_U U_k ⟶ U_j ×_U U_k`. -/
def pr12 (i j k : I) : triple Ui i j k ⟶ pair Ui j k :=
  Over.homMk (pr12Scheme Ui i j k) (pr12_w Ui i j k)

/-- The two legs of `pr02Scheme` agree over `U`. -/
theorem pr02Scheme_w (i j k : I) :
    (pullback.fst (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom) (Ui k).hom ≫
        pullback.fst (Ui i).hom (Ui j).hom) ≫
        (Ui i).hom =
      pullback.snd (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom)
          (Ui k).hom ≫
        (Ui k).hom := sorry

/-- Underlying scheme map of `pr₀₂`. -/
def pr02Scheme (i j k : I) : (triple Ui i j k).left ⟶ (pair Ui i k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom) (Ui k).hom ≫
      pullback.fst (Ui i).hom (Ui j).hom)
    (pullback.snd (pullback.fst (Ui i).hom (Ui j).hom ≫ (Ui i).hom) (Ui k).hom)
    (pr02Scheme_w Ui i j k)

/-- `pr02Scheme` lies over `U`. -/
theorem pr02_w (i j k : I) :
    pr02Scheme Ui i j k ≫ (pair Ui i k).hom = (triple Ui i j k).hom := sorry

/-- The projection `pr₀₂ : U_i ×_U U_j ×_U U_k ⟶ U_i ×_U U_k`. -/
def pr02 (i j k : I) : triple Ui i j k ⟶ pair Ui i k :=
  Over.homMk (pr02Scheme Ui i j k) (pr02_w Ui i j k)

/-- The two projections `U_ijk ⟶ U_j` agree. -/
theorem pr01_comp_pr1 (i j k : I) :
    pr01 Ui i j k ≫ pr1 Ui i j = pr12 Ui i j k ≫ pr0 Ui j k := sorry

/-- The two projections `U_ijk ⟶ U_i` agree. -/
theorem pr01_comp_pr0 (i j k : I) :
    pr01 Ui i j k ≫ pr0 Ui i j = pr02 Ui i j k ≫ pr0 Ui i k := sorry

/-- The two projections `U_ijk ⟶ U_k` agree. -/
theorem pr12_comp_pr1 (i j k : I) :
    pr12 Ui i j k ≫ pr1 Ui j k = pr02 Ui i j k ≫ pr1 Ui i k := sorry

/-- Restriction of an `H_{U_i}`-action along a morphism of schemes over `U`,
transported to an `H_{U_W}`-action. -/
def restrictAction {V W : Over U} (f : W ⟶ V)
    (X : Action (grpOverPullback H (base V))) :
    Action (grpOverPullback H (base W)) :=
  actionCongr
    ((grpOverPullbackCompIso (base V) (ofOverMap f) H).symm ≪≫
      eqToIso (congrArg (grpOverPullback H) (base_comp f)))
    (pullbackAction (ofOverMap f) (grpOverPullback H (base V)) X)

/-- Restriction of actions along a composite is the composite of restrictions. -/
def restrictAction_compIso {V W X : Over U} (f : X ⟶ W) (g : W ⟶ V)
    (Y : Action (grpOverPullback H (base V))) :
    restrictAction H (f ≫ g) Y ≅ restrictAction H f (restrictAction H g Y) :=
  { hom :=
      CategoryTheory.Mod.Hom.mk'
        (eqToHom (congrArg (fun t ↦ (Over.pullback t).obj Y.X) (ofOverMap_comp f g)) ≫
          ((Over.pullbackComp (ofOverMap f) (ofOverMap g)).app Y.X).hom)
        sorry
    inv :=
      CategoryTheory.Mod.Hom.mk'
        (((Over.pullbackComp (ofOverMap f) (ofOverMap g)).app Y.X).inv ≫
          eqToHom (congrArg (fun t ↦ (Over.pullback t).obj Y.X) (ofOverMap_comp f g).symm))
        sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Functoriality of `restrictAction` in the action. -/
def restrictAction_mapIso {V W : Over U} (f : W ⟶ V)
    {X Y : Action (grpOverPullback H (base V))} (e : X ≅ Y) :
    restrictAction H f X ≅ restrictAction H f Y :=
  { hom := CategoryTheory.Mod.Hom.mk' ((Over.pullback (ofOverMap f)).map e.hom.hom) sorry
    inv := CategoryTheory.Mod.Hom.mk' ((Over.pullback (ofOverMap f)).map e.inv.hom) sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The base change `X_i ×_U U_j` as an `H_{U_i ×_U U_j}`-action. -/
def leftRestrict (i j : I) (X : Action (grpOverPullback H (base (Ui i)))) :
    Action (grpOverPullback H (base (pair Ui i j))) :=
  restrictAction H (pr0 Ui i j) X

/-- The base change `U_i ×_U X_j` as an `H_{U_i ×_U U_j}`-action. -/
def rightRestrict (i j : I) (X : Action (grpOverPullback H (base (Ui j)))) :
    Action (grpOverPullback H (base (pair Ui i j))) :=
  restrictAction H (pr1 Ui i j) X

/-- Functoriality of `leftRestrict` in the local action. -/
def leftRestrict_mapIso (i j : I)
    {X Y : Action (grpOverPullback H (base (Ui i)))} (e : X ≅ Y) :
    leftRestrict Ui H i j X ≅ leftRestrict Ui H i j Y :=
  restrictAction_mapIso H (pr0 Ui i j) e

/-- Functoriality of `rightRestrict` in the local action. -/
def rightRestrict_mapIso (i j : I)
    {X Y : Action (grpOverPullback H (base (Ui j)))} (e : X ≅ Y) :
    rightRestrict Ui H i j X ≅ rightRestrict Ui H i j Y :=
  restrictAction_mapIso H (pr1 Ui i j) e

/-- The pairwise comparison of a descent isomorphism after restriction to a
triple overlap, along `pr₀₁`. -/
def isoRestrict₀₁ (i j k : I)
    {Xi : Action (grpOverPullback H (base (Ui i)))}
    {Xj : Action (grpOverPullback H (base (Ui j)))}
    (φ : leftRestrict Ui H i j Xi ≅ rightRestrict Ui H i j Xj) :
    restrictAction H (pr01 Ui i j k ≫ pr0 Ui i j) Xi ≅
      restrictAction H (pr01 Ui i j k ≫ pr1 Ui i j) Xj :=
  restrictAction_compIso H (pr01 Ui i j k) (pr0 Ui i j) Xi ≪≫
    restrictAction_mapIso H (pr01 Ui i j k) φ ≪≫
      (restrictAction_compIso H (pr01 Ui i j k) (pr1 Ui i j) Xj).symm

/-- The pairwise comparison of a descent isomorphism after restriction to a
triple overlap, along `pr₁₂`. -/
def isoRestrict₁₂ (i j k : I)
    {Xj : Action (grpOverPullback H (base (Ui j)))}
    {Xk : Action (grpOverPullback H (base (Ui k)))}
    (φ : leftRestrict Ui H j k Xj ≅ rightRestrict Ui H j k Xk) :
    restrictAction H (pr12 Ui i j k ≫ pr0 Ui j k) Xj ≅
      restrictAction H (pr12 Ui i j k ≫ pr1 Ui j k) Xk :=
  restrictAction_compIso H (pr12 Ui i j k) (pr0 Ui j k) Xj ≪≫
    restrictAction_mapIso H (pr12 Ui i j k) φ ≪≫
      (restrictAction_compIso H (pr12 Ui i j k) (pr1 Ui j k) Xk).symm

/-- The pairwise comparison of a descent isomorphism after restriction to a
triple overlap, along `pr₀₂`. -/
def isoRestrict₀₂ (i j k : I)
    {Xi : Action (grpOverPullback H (base (Ui i)))}
    {Xk : Action (grpOverPullback H (base (Ui k)))}
    (φ : leftRestrict Ui H i k Xi ≅ rightRestrict Ui H i k Xk) :
    restrictAction H (pr02 Ui i j k ≫ pr0 Ui i k) Xi ≅
      restrictAction H (pr02 Ui i j k ≫ pr1 Ui i k) Xk :=
  restrictAction_compIso H (pr02 Ui i j k) (pr0 Ui i k) Xi ≪≫
    restrictAction_mapIso H (pr02 Ui i j k) φ ≪≫
      (restrictAction_compIso H (pr02 Ui i j k) (pr1 Ui i k) Xk).symm

/-- The cocycle condition on a family of `H_{U_ij}`-equivariant isomorphisms,
after restriction to every `U_i ×_U U_j ×_U U_k`. -/
def IsCocycle (obj : ∀ i, Action (grpOverPullback H (base (Ui i))))
    (iso : ∀ i j, leftRestrict Ui H i j (obj i) ≅ rightRestrict Ui H i j (obj j)) :
    Prop :=
  ∀ i j k,
    isoRestrict₀₁ Ui H i j k (iso i j) ≪≫
        eqToIso (congrArg (fun t ↦ restrictAction H t (obj j)) (pr01_comp_pr1 Ui i j k)) ≪≫
          isoRestrict₁₂ Ui H i j k (iso j k) =
      eqToIso (congrArg (fun t ↦ restrictAction H t (obj i)) (pr01_comp_pr0 Ui i j k)) ≪≫
        isoRestrict₀₂ Ui H i j k (iso i k) ≪≫
          (eqToIso (congrArg (fun t ↦ restrictAction H t (obj k))
              (pr12_comp_pr1 Ui i j k))).symm

/-- Restriction of a global `H`-action along `U_W ⟶ U` versus restriction in
stages along `W ⟶ V ⟶ U`. -/
def restrictPullbackIso {V W : Over U} (f : W ⟶ V) (X : Action H) :
    restrictAction H f (pullbackAction (base V) H X) ≅ pullbackAction (base W) H X :=
  { hom :=
      CategoryTheory.Mod.Hom.mk'
        (((Over.pullbackComp (ofOverMap f) (base V)).app X.X).inv ≫
          eqToHom (congrArg (fun t ↦ (Over.pullback t).obj X.X) (base_comp f)))
        sorry
    inv :=
      CategoryTheory.Mod.Hom.mk'
        (eqToHom (congrArg (fun t ↦ (Over.pullback t).obj X.X) (base_comp f).symm) ≫
          ((Over.pullbackComp (ofOverMap f) (base V)).app X.X).hom)
        sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Canonical comparison `X_i ×_U U_j ≅ U_i ×_U X_j` of a global `H`-action. -/
def canonicalOverlap (X : Action H) (i j : I) :
    leftRestrict Ui H i j (pullbackAction (base (Ui i)) H X) ≅
      rightRestrict Ui H i j (pullbackAction (base (Ui j)) H X) :=
  restrictPullbackIso H (pr0 Ui i j) X ≪≫ (restrictPullbackIso H (pr1 Ui i j) X).symm

/-- Descent data for principal homogeneous spaces under a group algebraic space
along an fppf covering of schemes. -/
structure DescentDatum where
  /-- The family `{U_i → U}` is an fppf covering. -/
  covering : Scheme.FppfCovering Ui
  /-- The local `H_{U_i}`-actions `X_i` over `U_i`. -/
  obj : ∀ i, Action (grpOverPullback H (base (Ui i)))
  /-- Each `X_i` is a principal homogeneous `H_{U_i}`-space. -/
  isPrincipal : ∀ i, IsTorsor (grpOverPullback H (base (Ui i))) (obj i)
  /-- The `H_{U_i ×_U U_j}`-equivariant isomorphisms
  `φ_ij : X_i ×_U U_j ≅ U_i ×_U X_j`. -/
  iso : ∀ i j, leftRestrict Ui H i j (obj i) ≅ rightRestrict Ui H i j (obj j)
  /-- The family `φ_ij` satisfies the cocycle condition on every
  `U_i ×_U U_j ×_U U_k`. -/
  cocycle : IsCocycle Ui H obj iso

namespace DescentDatum

/-- Assemble descent data from an fppf covering, local principal homogeneous
spaces, equivariant overlap isomorphisms, and the cocycle condition. -/
def ofIso (covering : Scheme.FppfCovering Ui)
    (obj : ∀ i, Action (grpOverPullback H (base (Ui i))))
    (isPrincipal : ∀ i, IsTorsor (grpOverPullback H (base (Ui i))) (obj i))
    (iso : ∀ i j, leftRestrict Ui H i j (obj i) ≅ rightRestrict Ui H i j (obj j))
    (cocycle : IsCocycle Ui H obj iso) : DescentDatum Ui H where
  covering := covering
  obj := obj
  isPrincipal := isPrincipal
  iso := iso
  cocycle := cocycle

/-- The constructor `ofIso` stores the supplied covering and local actions. -/
theorem ofIso_spec (covering : Scheme.FppfCovering Ui)
    (obj : ∀ i, Action (grpOverPullback H (base (Ui i))))
    (isPrincipal : ∀ i, IsTorsor (grpOverPullback H (base (Ui i))) (obj i))
    (iso : ∀ i j, leftRestrict Ui H i j (obj i) ≅ rightRestrict Ui H i j (obj j))
    (cocycle : IsCocycle Ui H obj iso) :
    (ofIso Ui H covering obj isPrincipal iso cocycle).covering = covering ∧
      (ofIso Ui H covering obj isPrincipal iso cocycle).obj = obj := sorry

/-- The overlap isomorphisms stored by `ofIso` are the supplied family `φ_ij`. -/
theorem ofIso_iso (covering : Scheme.FppfCovering Ui)
    (obj : ∀ i, Action (grpOverPullback H (base (Ui i))))
    (isPrincipal : ∀ i, IsTorsor (grpOverPullback H (base (Ui i))) (obj i))
    (iso : ∀ i j, leftRestrict Ui H i j (obj i) ≅ rightRestrict Ui H i j (obj j))
    (cocycle : IsCocycle Ui H obj iso) :
    (ofIso Ui H covering obj isPrincipal iso cocycle).iso = iso := sorry

/-- Canonical descent data of a global principal homogeneous `H`-space along an
fppf covering. -/
def ofTorsor (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) : DescentDatum Ui H where
  covering := hUi
  obj := fun i ↦ pullbackAction (base (Ui i)) H X
  isPrincipal := fun i ↦ sorry
  iso := fun i j ↦ canonicalOverlap Ui H X i j
  cocycle := sorry

/-- The local objects of `ofTorsor` are the slice pullbacks of the global
action. -/
theorem ofTorsor_obj (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) (i : I) :
    (ofTorsor Ui H hUi X hX).obj i = pullbackAction (base (Ui i)) H X := sorry

/-- The covering stored by `ofTorsor` is the supplied fppf covering. -/
theorem ofTorsor_covering (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) :
    (ofTorsor Ui H hUi X hX).covering = hUi := sorry

/-- The overlap isomorphisms of `ofTorsor` are the canonical pullback
comparisons of `X`. -/
theorem ofTorsor_iso (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) (i j : I) :
    (ofTorsor Ui H hUi X hX).iso i j = canonicalOverlap Ui H X i j := sorry

/-- An effective realisation of descent data: a global principal homogeneous
`H`-space whose base changes recover the local spaces and the descent
isomorphisms `φ_ij`. -/
structure Effectiveness (D : DescentDatum Ui H) where
  /-- The global `H`-action over `U`. -/
  X : Action H
  /-- The global action is a principal homogeneous `H`-space. -/
  isPrincipal : IsTorsor H X
  /-- Base change of `X` to each `U_i` recovers `X_i`. -/
  iso : ∀ i, pullbackAction (base (Ui i)) H X ≅ D.obj i
  /-- The descent isomorphisms `φ_ij` are the comparisons of the base-change
  isomorphisms of `X`. -/
  recovers : ∀ i j,
    leftRestrict_mapIso Ui H i j (iso i) ≪≫ D.iso i j =
      canonicalOverlap Ui H X i j ≪≫ rightRestrict_mapIso Ui H i j (iso j)

/-- The identity datum of a global principal homogeneous `H`-space is effective,
realised by that same space. -/
def Effectiveness.ofTorsor (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) :
    (ofTorsor Ui H hUi X hX).Effectiveness where
  X := X
  isPrincipal := hX
  iso := fun i ↦ Iso.refl _
  recovers := sorry

/-- The global action stored by `Effectiveness.ofTorsor` is the original
action. -/
theorem Effectiveness.ofTorsor_X (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) :
    (Effectiveness.ofTorsor Ui H hUi X hX).X = X := sorry

/-- An effective realisation is a principal homogeneous `H`-space whose overlap
comparisons recover `φ_ij`. -/
theorem Effectiveness.spec {D : DescentDatum Ui H} (E : D.Effectiveness) :
    IsTorsor H E.X ∧
      ∀ i j,
        leftRestrict_mapIso Ui H i j (E.iso i) ≪≫ D.iso i j =
          canonicalOverlap Ui H E.X i j ≪≫
            rightRestrict_mapIso Ui H i j (E.iso j) := sorry

end DescentDatum

end AlgebraicGeometry.GroupAlgebraicSpace.Principal
