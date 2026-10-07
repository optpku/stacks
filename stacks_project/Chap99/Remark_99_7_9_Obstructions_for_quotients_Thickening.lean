module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap76.Lemma_76_5_3_Map
public import stacks_project.Chap76.Lemma_76_18_1_Thickening
public import stacks_project.Chap76.Lemma_76_9_8_Pullback
public import stacks_project.Chap99.«99_7_1_1_Functor»

/-!
# First-order thickenings of fibres of the quotient functor

A first-order thickening `T ⊂ T'` of schemes over `B` induces a first-order thickening
`X_T ⊂ X_{T'}` of algebraic spaces. The associated ideal sheaf `I` is a quotient of
`f_T^* J`. The source abbreviation `G ⊗_{O_T} J` is the monoidal tensor of `G` with
`f_T^* J`. Lemma 91.11.2 identifies `f_T^* J ⊗ F_T` with `I ⊗ F_T` only for `F_{T'}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A first-order thickening of schemes over `S` remains a first-order thickening after
passing to algebraic spaces via `ofOverMap`. -/
instance instIsFirstOrderThickening_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (g : U ⟶ V) [AlgebraicGeometry.IsFirstOrderThickening g.left] :
    IsFirstOrderThickening ((ofOverFunctor S).map g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The square comparing `X_T ⊂ X_{T'}` with `T ⊂ T'` over `B`. -/
theorem fiberMap_commSq (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ') :
    CommSq (pullback.snd f σ.hom) (fiberMap f h)
      ((ofOverFunctor S).map h.left) (pullback.snd f σ'.hom) :=
  sorry

/-- In Situation 99.7.1, a first-order thickening `T ⊂ T'` of schemes over `B` induces a
first-order thickening `X_T ⊂ X_{T'}`. -/
instance instIsFirstOrderThickening_fiberMap (f : X ⟶ B) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    IsFirstOrderThickening (fiberMap f h) :=
  sorry

/-- The pullback `f_T^* J` of the ideal sheaf of `T ⊂ T'` to `X_T`. -/
def pullbackIdeal (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ') :
    (fiber f σ).Modules :=
  (Modules.pullback (pullback.snd f σ.hom)).obj
    ((Modules.pullback ((ofOverFunctor S).map h.left)).obj
      (Hom.idealSheaf ((ofOverFunctor S).map h.left)))

/-- `pullbackIdeal` is the successive pullback of the ideal sheaf of `T ⊂ T'` along
`T' ⟶ T` and `X_T ⟶ T`. -/
theorem pullbackIdeal_eq (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ') :
    pullbackIdeal f h =
      (Modules.pullback (pullback.snd f σ.hom)).obj
        ((Modules.pullback ((ofOverFunctor S).map h.left)).obj
          (Hom.idealSheaf ((ofOverFunctor S).map h.left))) :=
  sorry

/-- The comparison `f_T^* J ⟶ i^* I` identifying the ideal sheaf of `X_T ⊂ X_{T'}` as a
quotient of `f_T^* J`. -/
def idealComparison (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    [IsFirstOrderThickening (fiberMap f h)]
    [IsFirstOrderThickening ((ofOverFunctor S).map h.left)] :
    pullbackIdeal f h ⟶
      (Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)) :=
  (Modules.pullbackComp (pullback.snd f σ.hom) ((ofOverFunctor S).map h.left)).hom.app
      (Hom.idealSheaf ((ofOverFunctor S).map h.left)) ≫
    eqToHom
      (congrArg (fun k ↦ (Modules.pullback k).obj
          (Hom.idealSheaf ((ofOverFunctor S).map h.left)))
        (fiberMap_snd f h).symm) ≫
    (Modules.pullbackComp (fiberMap f h) (pullback.snd f σ'.hom)).inv.app
      (Hom.idealSheaf ((ofOverFunctor S).map h.left)) ≫
    (Modules.pullback (fiberMap f h)).map
      (Hom.Conormal.pulledIdealToIdeal (fiberMap_commSq f h))

/-- The comparison `f_T^* J ⟶ i^* I` is an epimorphism, so `I` is a quotient of
`f_T^* J`. -/
instance instEpi_idealComparison (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    [IsFirstOrderThickening (fiberMap f h)] :
    Epi (idealComparison f h) :=
  sorry

/-- The commutative presentation of `I ⊗ i_* G` on `X_{T'}`. -/
def thickIdealTensor (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) : (fiber f σ').Modules :=
  Modules.ofComm
    (tensorObj
      (Modules.toCommSubobject (Hom.idealSheafSubobject (fiberMap f h)))
      (Modules.toComm ((Modules.pushforward (fiberMap f h)).obj G)))

/-- `thickIdealTensor` is `ofComm` of the commutative tensor of `I` with `i_* G`. -/
theorem thickIdealTensor_eq (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) :
    thickIdealTensor f h G =
      Modules.ofComm
        (tensorObj
          (Modules.toCommSubobject (Hom.idealSheafSubobject (fiberMap f h)))
          (Modules.toComm ((Modules.pushforward (fiberMap f h)).obj G))) :=
  sorry

/-- The source abbreviation `G ⊗_{O_T} J`, defined as `f_T^* J ⊗_{O_{X_T}} G`. -/
abbrev tensorIdeal (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    (G : (fiber f σ).Modules) : (fiber f σ).Modules :=
  tensorObj G (pullbackIdeal f h)

/-- `tensorIdeal f h G` is the monoidal tensor of `G` with `f_T^* J`. -/
theorem tensorIdeal_eq (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    (G : (fiber f σ).Modules) :
    tensorIdeal f h G = tensorObj G (pullbackIdeal f h) :=
  sorry

/-- Tensoring with `f_T^* J` is functorial in the `O_{X_T}`-module. -/
def tensorIdeal_map (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    {G H : (fiber f σ).Modules} (φ : G ⟶ H) :
    tensorIdeal f h G ⟶ tensorIdeal f h H :=
  tensorHom φ (𝟙 (pullbackIdeal f h))

/-- `tensorIdeal_map` is `tensorHom` with the identity on `pullbackIdeal`. -/
theorem tensorIdeal_map_eq (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    {G H : (fiber f σ).Modules} (φ : G ⟶ H) :
    tensorIdeal_map f h φ = tensorHom φ (𝟙 (pullbackIdeal f h)) :=
  sorry

/-- The comparison `G ⊗ f_T^* J ⟶ G ⊗ i^* I` induced by `idealComparison`. -/
def tensorIdeal_comparison (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) :
    tensorIdeal f h G ⟶
      tensorObj G ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h))) :=
  tensorHom (𝟙 G) (idealComparison f h)

/-- `tensorIdeal_comparison` is `tensorHom` of the identity with `idealComparison`. -/
theorem tensorIdeal_comparison_eq (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) :
    tensorIdeal_comparison f h G = tensorHom (𝟙 G) (idealComparison f h) :=
  sorry

/-- Braiding `G ⊗ f_T^* J ⟶ f_T^* J ⊗ G` of the algebraic-space module tensor. -/
def tensorIdeal_braiding (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    (G : (fiber f σ).Modules) :
    tensorIdeal f h G ⟶ tensorObj (pullbackIdeal f h) G :=
  (Modules.ofCommModules (fiber f σ)).map
    (β_ ((Modules.toCommModules (fiber f σ)).obj G)
      ((Modules.toCommModules (fiber f σ)).obj (pullbackIdeal f h))).hom

/-- `tensorIdeal_braiding` is the image of the commutative braiding under `ofCommModules`. -/
theorem tensorIdeal_braiding_eq (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    (G : (fiber f σ).Modules) :
    tensorIdeal_braiding f h G =
      (Modules.ofCommModules (fiber f σ)).map
        (β_ ((Modules.toCommModules (fiber f σ)).obj G)
          ((Modules.toCommModules (fiber f σ)).obj (pullbackIdeal f h))).hom :=
  sorry

/-- After braiding, `idealComparison` tensors on the left as
`f_T^* J ⊗ G ⟶ i^* I ⊗ G`. -/
def tensorIdeal_comparison_left (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) :
    tensorObj (pullbackIdeal f h) G ⟶
      tensorObj ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
        G :=
  tensorHom (idealComparison f h) (𝟙 G)

/-- `tensorIdeal_comparison_left` is `tensorHom` of `idealComparison` with the identity. -/
theorem tensorIdeal_comparison_left_eq (f : X ⟶ B) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) :
    tensorIdeal_comparison_left f h G = tensorHom (idealComparison f h) (𝟙 G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
