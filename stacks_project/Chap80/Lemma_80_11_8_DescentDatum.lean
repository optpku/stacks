module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Definition_78_9_3_Torsor
public import stacks_project.Chap80.Lemma_80_11_8_Pullback

/-!
# Descent data for fppf torsors under a group algebraic space

Chosen fibre-product descent data for fppf `G_i`-torsors along an fppf covering
of a scheme, including the canonical datum of a global torsor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open GroupAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupAlgebraicSpace.Torsor

variable {S : Scheme.{u}}

/-- Yoneda of a composite morphism of schemes over `S` is the composite. -/
theorem ofOverMap_comp {U V W : Over S} (f : U ⟶ V) (g : V ⟶ W) :
    ofOverMap (f ≫ g) = ofOverMap f ≫ ofOverMap g :=
  CategoryTheory.Functor.map_comp yoneda f g

/-- Yoneda of an identity morphism of schemes over `S` is the identity. -/
theorem ofOverMap_id (U : Over S) :
    ofOverMap (𝟙 U) = 𝟙 (ofOver U) :=
  CategoryTheory.Functor.map_id yoneda U

/-- The structure morphism `U ⟶ S` as a morphism of schemes over `S`. -/
def overToBase (U : Over S) : U ⟶ Over.mk (𝟙 S) :=
  Over.homMk U.hom (Category.comp_id U.hom)

/-- Morphisms to `Over.mk (𝟙 S)` are unique. -/
theorem overToBase_unique (U : Over S) (f : U ⟶ Over.mk (𝟙 S)) :
    f = overToBase U :=
  Over.mkIdTerminal.hom_ext f (overToBase U)

/-- The morphism `S_i ⟶ S` of algebraic spaces over `S`. -/
def base (U : Over S) : ofOver U ⟶ ofOver (Over.mk (𝟙 S)) :=
  ofOverMap (overToBase U)

/-- `base U` is `ofOverMap` of `overToBase U`. -/
theorem base_eq (U : Over S) : base U = ofOverMap (overToBase U) := sorry

/-- Pulling `S_i ⟶ S` back along `U ⟶ S_i` recovers `U ⟶ S`. -/
theorem base_comp {U V : Over S} (f : U ⟶ V) : ofOverMap f ≫ base V = base U :=
  (ofOverMap_comp f (overToBase V)).symm.trans
    (congrArg ofOverMap (overToBase_unique U (f ≫ overToBase V)))

variable {I : Type v} (Si : I → Over S)
variable (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 S))))

/-- The fibre product `S_i ×_S S_j` as a scheme over `S`. -/
def pair (i j : I) : Over S :=
  Over.mk (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom)

/-- Compatibility of `pr1` with the structure morphisms to `S`. -/
theorem pr1_w (i j : I) :
    pullback.snd (Si i).hom (Si j).hom ≫ (Si j).hom = (pair Si i j).hom := sorry

/-- The projection `pr₀ : S_i ×_S S_j ⟶ S_i`. -/
def pr0 (i j : I) : pair Si i j ⟶ Si i :=
  Over.homMk (pullback.fst (Si i).hom (Si j).hom) rfl

/-- The projection `pr₁ : S_i ×_S S_j ⟶ S_j`. -/
def pr1 (i j : I) : pair Si i j ⟶ Si j :=
  Over.homMk (pullback.snd (Si i).hom (Si j).hom) (pr1_w Si i j)

/-- `pr0` is induced by `pullback.fst`. -/
theorem pr0_eq (i j : I) :
    pr0 Si i j = Over.homMk (pullback.fst (Si i).hom (Si j).hom) rfl := sorry

/-- `pr1` is induced by `pullback.snd`. -/
theorem pr1_eq (i j : I) :
    pr1 Si i j = Over.homMk (pullback.snd (Si i).hom (Si j).hom) (pr1_w Si i j) := sorry

/-- The triple fibre product `S_i ×_S S_j ×_S S_k` as
`(S_i ×_S S_j) ×_S S_k` over `S`. -/
def triple (i j k : I) : Over S :=
  Over.mk
    (pullback.fst (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom) (Si k).hom ≫
      (pair Si i j).hom)

/-- The projection `pr₀₁ : S_i ×_S S_j ×_S S_k ⟶ S_i ×_S S_j`. -/
def pr01 (i j k : I) : triple Si i j k ⟶ pair Si i j :=
  Over.homMk
    (pullback.fst (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom) (Si k).hom) rfl

/-- The two legs of `pr12Scheme` agree over `S`. -/
theorem pr12Scheme_w (i j k : I) :
    (pullback.fst (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom) (Si k).hom ≫
        pullback.snd (Si i).hom (Si j).hom) ≫
        (Si j).hom =
      pullback.snd (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom)
          (Si k).hom ≫
        (Si k).hom := sorry

/-- Underlying scheme map of `pr₁₂`. -/
def pr12Scheme (i j k : I) : (triple Si i j k).left ⟶ (pair Si j k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom) (Si k).hom ≫
      pullback.snd (Si i).hom (Si j).hom)
    (pullback.snd (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom) (Si k).hom)
    (pr12Scheme_w Si i j k)

/-- `pr12Scheme` lies over `S`. -/
theorem pr12_w (i j k : I) :
    pr12Scheme Si i j k ≫ (pair Si j k).hom = (triple Si i j k).hom := sorry

/-- The projection `pr₁₂ : S_i ×_S S_j ×_S S_k ⟶ S_j ×_S S_k`. -/
def pr12 (i j k : I) : triple Si i j k ⟶ pair Si j k :=
  Over.homMk (pr12Scheme Si i j k) (pr12_w Si i j k)

/-- The two legs of `pr02Scheme` agree over `S`. -/
theorem pr02Scheme_w (i j k : I) :
    (pullback.fst (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom) (Si k).hom ≫
        pullback.fst (Si i).hom (Si j).hom) ≫
        (Si i).hom =
      pullback.snd (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom)
          (Si k).hom ≫
        (Si k).hom := sorry

/-- Underlying scheme map of `pr₀₂`. -/
def pr02Scheme (i j k : I) : (triple Si i j k).left ⟶ (pair Si i k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom) (Si k).hom ≫
      pullback.fst (Si i).hom (Si j).hom)
    (pullback.snd (pullback.fst (Si i).hom (Si j).hom ≫ (Si i).hom) (Si k).hom)
    (pr02Scheme_w Si i j k)

/-- `pr02Scheme` lies over `S`. -/
theorem pr02_w (i j k : I) :
    pr02Scheme Si i j k ≫ (pair Si i k).hom = (triple Si i j k).hom := sorry

/-- The projection `pr₀₂ : S_i ×_S S_j ×_S S_k ⟶ S_i ×_S S_k`. -/
def pr02 (i j k : I) : triple Si i j k ⟶ pair Si i k :=
  Over.homMk (pr02Scheme Si i j k) (pr02_w Si i j k)

/-- The two projections `S_ijk ⟶ S_j` agree. -/
theorem pr01_comp_pr1 (i j k : I) :
    pr01 Si i j k ≫ pr1 Si i j = pr12 Si i j k ≫ pr0 Si j k := sorry

/-- The two projections `S_ijk ⟶ S_i` agree. -/
theorem pr01_comp_pr0 (i j k : I) :
    pr01 Si i j k ≫ pr0 Si i j = pr02 Si i j k ≫ pr0 Si i k := sorry

/-- The two projections `S_ijk ⟶ S_k` agree. -/
theorem pr12_comp_pr1 (i j k : I) :
    pr12 Si i j k ≫ pr1 Si j k = pr02 Si i j k ≫ pr1 Si i k := sorry

/-- Restriction of a `G_{S_i}`-action along a morphism of schemes over `S`,
transported to a `G_{S_U}`-action. -/
def restrictAction {U V : Over S} (f : U ⟶ V)
    (X : Action (grpOverPullback G (base V))) :
    Action (grpOverPullback G (base U)) :=
  actionCongr
    ((grpOverPullbackCompIso (base V) (ofOverMap f) G).symm ≪≫
      eqToIso (congrArg (grpOverPullback G) (base_comp f)))
    (pullbackAction (ofOverMap f) (grpOverPullback G (base V)) X)

/-- The underlying object of `restrictAction f X` is the slice pullback of `X`. -/
theorem restrictAction_X {U V : Over S} (f : U ⟶ V)
    (X : Action (grpOverPullback G (base V))) :
    (restrictAction G f X).X = (overPullback (ofOverMap f)).obj X.X := sorry

/-- Restriction of actions along a composite is the composite of restrictions. -/
def restrictAction_compIso {U V W : Over S} (f : U ⟶ V) (g : V ⟶ W)
    (X : Action (grpOverPullback G (base W))) :
    restrictAction G (f ≫ g) X ≅ restrictAction G f (restrictAction G g X) :=
  { hom :=
      CategoryTheory.Mod.Hom.mk'
        (eqToHom (congrArg (fun t ↦ (overPullback t).obj X.X) (ofOverMap_comp f g)) ≫
          ((overPullbackCompIso (ofOverMap g) (ofOverMap f)).app X.X).hom)
        sorry
    inv :=
      CategoryTheory.Mod.Hom.mk'
        (((overPullbackCompIso (ofOverMap g) (ofOverMap f)).app X.X).inv ≫
          eqToHom (congrArg (fun t ↦ (overPullback t).obj X.X) (ofOverMap_comp f g).symm))
        sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Functoriality of `restrictAction` in the action. -/
def restrictAction_mapIso {U V : Over S} (f : U ⟶ V)
    {X Y : Action (grpOverPullback G (base V))} (e : X ≅ Y) :
    restrictAction G f X ≅ restrictAction G f Y :=
  { hom := CategoryTheory.Mod.Hom.mk' ((overPullback (ofOverMap f)).map e.hom.hom) sorry
    inv := CategoryTheory.Mod.Hom.mk' ((overPullback (ofOverMap f)).map e.inv.hom) sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The base change `X_i ×_S S_j` as a `G_{S_i ×_S S_j}`-action. -/
def leftRestrict (i j : I) (X : Action (grpOverPullback G (base (Si i)))) :
    Action (grpOverPullback G (base (pair Si i j))) :=
  restrictAction G (pr0 Si i j) X

/-- The base change `S_i ×_S X_j` as a `G_{S_i ×_S S_j}`-action. -/
def rightRestrict (i j : I) (X : Action (grpOverPullback G (base (Si j)))) :
    Action (grpOverPullback G (base (pair Si i j))) :=
  restrictAction G (pr1 Si i j) X

/-- Functoriality of `leftRestrict` in the local action. -/
def leftRestrict_mapIso (i j : I)
    {X Y : Action (grpOverPullback G (base (Si i)))} (e : X ≅ Y) :
    leftRestrict Si G i j X ≅ leftRestrict Si G i j Y :=
  restrictAction_mapIso G (pr0 Si i j) e

/-- Functoriality of `rightRestrict` in the local action. -/
def rightRestrict_mapIso (i j : I)
    {X Y : Action (grpOverPullback G (base (Si j)))} (e : X ≅ Y) :
    rightRestrict Si G i j X ≅ rightRestrict Si G i j Y :=
  restrictAction_mapIso G (pr1 Si i j) e

/-- `leftRestrict` is restriction along `pr0`. -/
theorem leftRestrict_eq (i j : I) (X : Action (grpOverPullback G (base (Si i)))) :
    leftRestrict Si G i j X = restrictAction G (pr0 Si i j) X := sorry

/-- `rightRestrict` is restriction along `pr1`. -/
theorem rightRestrict_eq (i j : I) (X : Action (grpOverPullback G (base (Si j)))) :
    rightRestrict Si G i j X = restrictAction G (pr1 Si i j) X := sorry

/-- The pairwise comparison of a descent isomorphism after restriction to a
triple overlap, along `pr₀₁`. -/
def isoRestrict₀₁ (i j k : I)
    {Xi : Action (grpOverPullback G (base (Si i)))}
    {Xj : Action (grpOverPullback G (base (Si j)))}
    (φ : leftRestrict Si G i j Xi ≅ rightRestrict Si G i j Xj) :
    restrictAction G (pr01 Si i j k ≫ pr0 Si i j) Xi ≅
      restrictAction G (pr01 Si i j k ≫ pr1 Si i j) Xj :=
  restrictAction_compIso G (pr01 Si i j k) (pr0 Si i j) Xi ≪≫
    restrictAction_mapIso G (pr01 Si i j k) φ ≪≫
      (restrictAction_compIso G (pr01 Si i j k) (pr1 Si i j) Xj).symm

/-- The pairwise comparison of a descent isomorphism after restriction to a
triple overlap, along `pr₁₂`. -/
def isoRestrict₁₂ (i j k : I)
    {Xj : Action (grpOverPullback G (base (Si j)))}
    {Xk : Action (grpOverPullback G (base (Si k)))}
    (φ : leftRestrict Si G j k Xj ≅ rightRestrict Si G j k Xk) :
    restrictAction G (pr12 Si i j k ≫ pr0 Si j k) Xj ≅
      restrictAction G (pr12 Si i j k ≫ pr1 Si j k) Xk :=
  restrictAction_compIso G (pr12 Si i j k) (pr0 Si j k) Xj ≪≫
    restrictAction_mapIso G (pr12 Si i j k) φ ≪≫
      (restrictAction_compIso G (pr12 Si i j k) (pr1 Si j k) Xk).symm

/-- The pairwise comparison of a descent isomorphism after restriction to a
triple overlap, along `pr₀₂`. -/
def isoRestrict₀₂ (i j k : I)
    {Xi : Action (grpOverPullback G (base (Si i)))}
    {Xk : Action (grpOverPullback G (base (Si k)))}
    (φ : leftRestrict Si G i k Xi ≅ rightRestrict Si G i k Xk) :
    restrictAction G (pr02 Si i j k ≫ pr0 Si i k) Xi ≅
      restrictAction G (pr02 Si i j k ≫ pr1 Si i k) Xk :=
  restrictAction_compIso G (pr02 Si i j k) (pr0 Si i k) Xi ≪≫
    restrictAction_mapIso G (pr02 Si i j k) φ ≪≫
      (restrictAction_compIso G (pr02 Si i j k) (pr1 Si i k) Xk).symm

/-- The cocycle condition on a family of `G_{S_ij}`-equivariant isomorphisms,
after restriction to every `S_i ×_S S_j ×_S S_k`. -/
def IsCocycle (obj : ∀ i, Action (grpOverPullback G (base (Si i))))
    (iso : ∀ i j, leftRestrict Si G i j (obj i) ≅ rightRestrict Si G i j (obj j)) :
    Prop :=
  ∀ i j k,
    isoRestrict₀₁ Si G i j k (iso i j) ≪≫
        eqToIso (congrArg (fun t ↦ restrictAction G t (obj j)) (pr01_comp_pr1 Si i j k)) ≪≫
          isoRestrict₁₂ Si G i j k (iso j k) =
      eqToIso (congrArg (fun t ↦ restrictAction G t (obj i)) (pr01_comp_pr0 Si i j k)) ≪≫
        isoRestrict₀₂ Si G i j k (iso i k) ≪≫
          (eqToIso (congrArg (fun t ↦ restrictAction G t (obj k))
              (pr12_comp_pr1 Si i j k))).symm

/-- Restriction of a global `G`-action along `S_U ⟶ S` versus restriction in
stages along `U ⟶ V ⟶ S`. -/
def restrictPullbackIso {U V : Over S} (f : U ⟶ V) (X : Action G) :
    restrictAction G f (pullbackAction (base V) G X) ≅ pullbackAction (base U) G X :=
  { hom :=
      CategoryTheory.Mod.Hom.mk'
        (((overPullbackCompIso (base V) (ofOverMap f)).app X.X).inv ≫
          eqToHom (congrArg (fun t ↦ (overPullback t).obj X.X) (base_comp f)))
        sorry
    inv :=
      CategoryTheory.Mod.Hom.mk'
        (eqToHom (congrArg (fun t ↦ (overPullback t).obj X.X) (base_comp f).symm) ≫
          ((overPullbackCompIso (base V) (ofOverMap f)).app X.X).hom)
        sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Canonical comparison `X_i ×_S S_j ≅ S_i ×_S X_j` of a global `G`-action. -/
def canonicalOverlap (X : Action G) (i j : I) :
    leftRestrict Si G i j (pullbackAction (base (Si i)) G X) ≅
      rightRestrict Si G i j (pullbackAction (base (Si j)) G X) :=
  restrictPullbackIso G (pr0 Si i j) X ≪≫ (restrictPullbackIso G (pr1 Si i j) X).symm

/-- Descent data for fppf torsors under a group algebraic space along an fppf
covering of schemes. -/
structure DescentDatum where
  /-- The family `{S_i → S}` is an fppf covering. -/
  covering : Scheme.FppfCovering Si
  /-- The local `G_i`-actions `X_i` over `S_i`. -/
  obj : ∀ i, Action (grpOverPullback G (base (Si i)))
  /-- Each `X_i` is an fppf `G_i`-torsor. -/
  isTorsor : ∀ i, IsStandardTorsor (grpOverPullback G (base (Si i))) (obj i) .fppf
  /-- The `G_{S_i ×_S S_j}`-equivariant isomorphisms
  `φ_ij : X_i ×_S S_j ≅ S_i ×_S X_j`. -/
  iso : ∀ i j, leftRestrict Si G i j (obj i) ≅ rightRestrict Si G i j (obj j)
  /-- The family `φ_ij` satisfies the cocycle condition on every
  `S_i ×_S S_j ×_S S_k`. -/
  cocycle : IsCocycle Si G obj iso

namespace DescentDatum

/-- Assemble descent data from an fppf covering, local torsors, equivariant
overlap isomorphisms, and the cocycle condition. -/
def ofIso (covering : Scheme.FppfCovering Si)
    (obj : ∀ i, Action (grpOverPullback G (base (Si i))))
    (isTorsor : ∀ i, IsStandardTorsor (grpOverPullback G (base (Si i))) (obj i) .fppf)
    (iso : ∀ i j, leftRestrict Si G i j (obj i) ≅ rightRestrict Si G i j (obj j))
    (cocycle : IsCocycle Si G obj iso) : DescentDatum Si G where
  covering := covering
  obj := obj
  isTorsor := isTorsor
  iso := iso
  cocycle := cocycle

/-- The constructor `ofIso` stores the supplied covering and local actions. -/
theorem ofIso_spec (covering : Scheme.FppfCovering Si)
    (obj : ∀ i, Action (grpOverPullback G (base (Si i))))
    (isTorsor : ∀ i, IsStandardTorsor (grpOverPullback G (base (Si i))) (obj i) .fppf)
    (iso : ∀ i j, leftRestrict Si G i j (obj i) ≅ rightRestrict Si G i j (obj j))
    (cocycle : IsCocycle Si G obj iso) :
    (ofIso Si G covering obj isTorsor iso cocycle).covering = covering ∧
      (ofIso Si G covering obj isTorsor iso cocycle).obj = obj := sorry

/-- The overlap isomorphisms stored by `ofIso` are the supplied family `φ_ij`. -/
theorem ofIso_iso (covering : Scheme.FppfCovering Si)
    (obj : ∀ i, Action (grpOverPullback G (base (Si i))))
    (isTorsor : ∀ i, IsStandardTorsor (grpOverPullback G (base (Si i))) (obj i) .fppf)
    (iso : ∀ i j, leftRestrict Si G i j (obj i) ≅ rightRestrict Si G i j (obj j))
    (cocycle : IsCocycle Si G obj iso) :
    (ofIso Si G covering obj isTorsor iso cocycle).iso = iso := sorry

/-- Canonical descent data of a global fppf `G`-torsor along an fppf covering. -/
def ofTorsor (hSi : Scheme.FppfCovering Si) (X : Action G)
    (hX : IsStandardTorsor G X .fppf) : DescentDatum Si G where
  covering := hSi
  obj := fun i ↦ pullbackAction (base (Si i)) G X
  isTorsor := fun i ↦ sorry
  iso := fun i j ↦ canonicalOverlap Si G X i j
  cocycle := sorry

/-- The local objects of `ofTorsor` are the slice pullbacks of the global
action. -/
theorem ofTorsor_obj (hSi : Scheme.FppfCovering Si) (X : Action G)
    (hX : IsStandardTorsor G X .fppf) (i : I) :
    (ofTorsor Si G hSi X hX).obj i = pullbackAction (base (Si i)) G X := sorry

/-- The covering stored by `ofTorsor` is the supplied fppf covering. -/
theorem ofTorsor_covering (hSi : Scheme.FppfCovering Si) (X : Action G)
    (hX : IsStandardTorsor G X .fppf) :
    (ofTorsor Si G hSi X hX).covering = hSi := sorry

/-- The overlap isomorphisms of `ofTorsor` are the canonical pullback
comparisons of `X`. -/
theorem ofTorsor_iso (hSi : Scheme.FppfCovering Si) (X : Action G)
    (hX : IsStandardTorsor G X .fppf) (i j : I) :
    (ofTorsor Si G hSi X hX).iso i j = canonicalOverlap Si G X i j := sorry

/-- An effective realisation of descent data: a global fppf `G`-torsor whose
base changes recover the local torsors and the descent isomorphisms `φ_ij`. -/
structure Effectiveness (D : DescentDatum Si G) where
  /-- The global `G`-action over `S`. -/
  X : Action G
  /-- The global action is an fppf `G`-torsor. -/
  isTorsor : IsStandardTorsor G X .fppf
  /-- Base change of `X` to each `S_i` recovers `X_i`. -/
  iso : ∀ i, pullbackAction (base (Si i)) G X ≅ D.obj i
  /-- The descent isomorphisms `φ_ij` are the comparisons of the base-change
  isomorphisms of `X`. -/
  recovers : ∀ i j,
    leftRestrict_mapIso Si G i j (iso i) ≪≫ D.iso i j =
      canonicalOverlap Si G X i j ≪≫ rightRestrict_mapIso Si G i j (iso j)

/-- The identity datum of a global fppf `G`-torsor is effective, realised by
that same torsor. -/
def Effectiveness.ofTorsor (hSi : Scheme.FppfCovering Si) (X : Action G)
    (hX : IsStandardTorsor G X .fppf) :
    (ofTorsor Si G hSi X hX).Effectiveness where
  X := X
  isTorsor := hX
  iso := fun i ↦ Iso.refl _
  recovers := sorry

/-- The global action stored by `Effectiveness.ofTorsor` is the original
action. -/
theorem Effectiveness.ofTorsor_X (hSi : Scheme.FppfCovering Si) (X : Action G)
    (hX : IsStandardTorsor G X .fppf) :
    (Effectiveness.ofTorsor Si G hSi X hX).X = X := sorry

/-- An effective realisation is an fppf `G`-torsor whose overlap comparisons
recover `φ_ij`. -/
theorem Effectiveness.spec {D : DescentDatum Si G} (E : D.Effectiveness) :
    IsStandardTorsor G E.X .fppf ∧
      ∀ i j,
        leftRestrict_mapIso Si G i j (E.iso i) ≪≫ D.iso i j =
          canonicalOverlap Si G E.X i j ≪≫
            rightRestrict_mapIso Si G i j (E.iso j) := sorry

/-- Effectiveness of fppf-torsor descent data is equivalent to existence of a
global fppf `G`-torsor recovering the local torsors and the descent
isomorphisms `φ_ij`. -/
theorem exists_fppfTorsor_iff [Small.{u} I] (D : DescentDatum Si G) :
    Nonempty D.Effectiveness ↔
      ∃ X : Action G,
        IsStandardTorsor G X .fppf ∧
          ∃ e : ∀ i, pullbackAction (base (Si i)) G X ≅ D.obj i,
            ∀ i j,
              leftRestrict_mapIso Si G i j (e i) ≪≫ D.iso i j =
                canonicalOverlap Si G X i j ≪≫
                  rightRestrict_mapIso Si G i j (e j) := sorry

end DescentDatum

end AlgebraicGeometry.GroupAlgebraicSpace.Torsor
