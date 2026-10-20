module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.ChangeOfBase

/-!
# Change of base for presentations of algebraic spaces

Presentations transport along morphisms of base schemes by composition or pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Presentation

/-- An internal equivalence relation from a represented kernel pair: the reflexivity, symmetry
and transitivity morphisms are the Yoneda preimages of the actual kernel-pair lifts. -/
def equivalenceRelationOfYonedaKernelPair {S : Scheme.{u}} {U R : Over S}
    {G : (Over S)ᵒᵖ ⥤ Type u} {f : yoneda.obj U ⟶ G} {p₁ p₂ : R ⟶ U}
    (k : IsKernelPair f (yoneda.map p₁) (yoneda.map p₂)) : EquivalenceRelation p₁ p₂ where
  right_cancellation := by sorry
  r := Yoneda.fullyFaithful.preimage (k.lift (𝟙 _) (𝟙 _) rfl)
  reflexivity₁ := by sorry
  reflexivity₂ := by sorry
  s := Yoneda.fullyFaithful.preimage (k.lift (yoneda.map p₂) (yoneda.map p₁) k.w.symm)
  symmetry₁ := by sorry
  symmetry₂ := by sorry
  c := PullbackCone.mk (pullback.fst p₂ p₁) (pullback.snd p₂ p₁) pullback.condition
  isLimit := pullbackIsPullback p₂ p₁
  t := Yoneda.fullyFaithful.preimage
    (k.lift (yoneda.map (pullback.fst p₂ p₁ ≫ p₁)) (yoneda.map (pullback.snd p₂ p₁ ≫ p₂))
      (by sorry))
  transitivity₁ := by sorry
  transitivity₂ := by sorry

/-- The point of `j(R)` over two points of `j(U)` with the same image in `j_!F`: split off their
common index, apply the original kernel-pair lift of `P`, and view the result over `S'`. -/
def extendBaseKernelPairLift {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) {V : Over S'} (x y : V ⟶ (Over.map g).obj P.U)
    (h : ((extendBasePresheafYonedaIso g P.U).inv ≫ extendBasePresheafMap g P.atlas).app
      (op V) x = ((extendBasePresheafYonedaIso g P.U).inv ≫ extendBasePresheafMap g P.atlas).app
      (op V) y) :
    V ⟶ (Over.map g).obj P.R.left :=
  let φx := AlgebraicSpace.indexOfHom g x
  let φy := AlgebraicSpace.indexOfHom g y
  let x₀ : Over.mk φx.left ⟶ P.U := AlgebraicSpace.homOverOfHom g x
  let y₀ : Over.mk φy.left ⟶ P.U := AlgebraicSpace.homOverOfHom g y
  have h' : (extendBasePresheafMap g P.atlas).app (op V)
      ⟨φx, x₀⟩ = (extendBasePresheafMap g P.atlas).app (op V) ⟨φy, y₀⟩ := by
    simpa [CategoryTheory.NatTrans.comp_app,
      extendBasePresheafYonedaIso_inv_apply, φx, φy, x₀, y₀] using h
  have hmap :
      (⟨φx, P.atlas.app (op (Over.mk φx.left)) x₀⟩ :
        Σ φ : V ⟶ Over.mk g, F.functorOfPoints.obj (op (Over.mk φ.left))) =
      ⟨φy, P.atlas.app (op (Over.mk φy.left)) y₀⟩ := by
    change (⟨φx, P.atlas.app (op (Over.mk φx.left)) x₀⟩ :
      Σ φ : V ⟶ Over.mk g, F.functorOfPoints.obj (op (Over.mk φ.left))) =
      ⟨φy, P.atlas.app (op (Over.mk φy.left)) y₀⟩ at h'
    exact h'
  have hidx : φx = φy := (Sigma.ext_iff.mp hmap).1
  let y₀' : Over.mk φx.left ⟶ P.U := Eq.mp
    (congrArg (fun ψ : V ⟶ Over.mk g => Over.mk ψ.left ⟶ P.U) hidx.symm) y₀
  have h_atlas_heq : HEq (P.atlas.app (op (Over.mk φx.left)) x₀)
      (P.atlas.app (op (Over.mk φy.left)) y₀) := (Sigma.ext_iff.mp hmap).2
  have transport : ∀ {φx φy : V ⟶ Over.mk g}
      (x : Over.mk φx.left ⟶ P.U) (y : Over.mk φy.left ⟶ P.U)
      (hidx : φx = φy),
      HEq (P.atlas.app (op (Over.mk φx.left)) x)
        (P.atlas.app (op (Over.mk φy.left)) y) →
      P.atlas.app (op (Over.mk φx.left)) x =
        P.atlas.app (op (Over.mk φx.left))
          (Eq.mp (congrArg (fun ψ : V ⟶ Over.mk g => Over.mk ψ.left ⟶ P.U)
            hidx.symm) y) := by
    intro φx φy x y hidx hxy
    cases hidx
    exact eq_of_heq hxy
  have h_atlas : P.atlas.app (op (Over.mk φx.left)) x₀ =
      P.atlas.app (op (Over.mk φx.left)) y₀' := by
    exact transport x₀ y₀ hidx h_atlas_heq
  let z := AlgebraicSpace.pullbackPoint
    (P.isKernelPair.app (op (Over.mk φx.left)))
    (show (yoneda.obj P.U).obj (op (Over.mk φx.left)) from x₀)
    (show (yoneda.obj P.U).obj (op (Over.mk φx.left)) from y₀') h_atlas
  AlgebraicSpace.homOfIndex g φx z

/-- View a presentation over a new base by composing its scheme structure maps. -/
def extendBase {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) : Presentation (AlgebraicSpace.extendBase g F) :=
  let scheme := (Over.map g).obj P.U
  let relation := P.R.viewedOver g
  let atlas : yoneda.obj scheme ⟶ (AlgebraicSpace.extendBase g F).functorOfPoints :=
    (extendBasePresheafYonedaIso g P.U).inv ≫ extendBasePresheafMap g P.atlas
  let isKernelPair : IsKernelPair atlas (yoneda.map relation.t) (yoneda.map relation.s) :=
    AlgebraicSpace.isPullback_of_pointLift _ _ _ _ (by sorry)
      (fun V x y h ↦ show V.unop ⟶ relation.left from extendBaseKernelPairLift g P x y h)
      (by sorry) (by sorry) (by sorry)
  { U := scheme
    R := relation
    atlas := atlas
    isEtaleEquivalence :=
      { isEquivalenceRelation :=
          (equivalenceRelationOfYonedaKernelPair isKernelPair).isEquivalenceRelation
        etale_t := by sorry
        etale_s := by sorry }
    atlas_etale := AlgebraicSpace.extendBasePresheafYonedaMap_etale g P.atlas_etale
    atlas_locallySurjective := by sorry
    isKernelPair := isKernelPair }

/-- The presenting scheme of `Presentation.extendBase g P` is `j(P.U)`. -/
@[simp]
theorem extendBase_U {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) :
    (P.extendBase g).U = (Over.map g).obj P.U := sorry

/-- The relation of `Presentation.extendBase g P` is `j(P.R)`. -/
@[simp]
theorem extendBase_R {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) :
    (P.extendBase g).R = P.R.viewedOver g := sorry

/-- The atlas of `Presentation.extendBase g P` is the transport of `P.atlas` along the
representable identification `h_{j(U)} ≅ j_! h_U`. -/
theorem extendBase_atlas {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) :
    (P.extendBase g).atlas =
      (extendBasePresheafYonedaIso g P.U).inv ≫ extendBasePresheafMap g P.atlas := sorry

/-- The point of `R'_S` over two points of `U'_S` with the same image in `j^{-1}F'`: transpose
them along `Over.map g ⊣ Over.pullback g`, apply the original kernel-pair lift of `P`, and
transpose back. -/
def baseChangeKernelPairLift {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') {V : Over S} (x y : V ⟶ (Over.pullback g).obj P.U)
    (h : ((baseChangePresheafYonedaIso g P.U).inv ≫
      Functor.whiskerLeft (Over.map g).op P.atlas).app (op V) x =
      ((baseChangePresheafYonedaIso g P.U).inv ≫
      Functor.whiskerLeft (Over.map g).op P.atlas).app (op V) y) :
    V ⟶ (Over.pullback g).obj P.R.left :=
  let adj := Over.mapPullbackAdj g
  let x' : (yoneda.obj P.U).obj (op ((Over.map g).obj V)) := (adj.homEquiv V P.U).symm x
  let y' : (yoneda.obj P.U).obj (op ((Over.map g).obj V)) := (adj.homEquiv V P.U).symm y
  have h_atlas : P.atlas.app (op ((Over.map g).obj V)) x' =
      P.atlas.app (op ((Over.map g).obj V)) y' := by
    change P.atlas.app (op ((Over.map g).obj V)) x' =
      P.atlas.app (op ((Over.map g).obj V)) y' at h
    exact h
  let z := AlgebraicSpace.pullbackPoint (P.isKernelPair.app (op ((Over.map g).obj V)))
    x' y' h_atlas
  adj.homEquiv V P.R.left z

/-- Pull a presentation back along a morphism of base schemes. -/
def baseChange {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') : Presentation (AlgebraicSpace.baseChange g F') :=
  let scheme := (Over.pullback g).obj P.U
  let relation := P.R.baseChange g
  let atlas : yoneda.obj scheme ⟶ (AlgebraicSpace.baseChange g F').functorOfPoints :=
    (baseChangePresheafYonedaIso g P.U).inv ≫
      Functor.whiskerLeft (Over.map g).op P.atlas
  let isKernelPair : IsKernelPair atlas (yoneda.map relation.t) (yoneda.map relation.s) :=
    AlgebraicSpace.isPullback_of_pointLift _ _ _ _ (by sorry)
      (fun V x y h ↦ show V.unop ⟶ relation.left from baseChangeKernelPairLift g P x y h)
      (by sorry) (by sorry) (by sorry)
  { U := scheme
    R := relation
    atlas := atlas
    isEtaleEquivalence :=
      { isEquivalenceRelation :=
          (equivalenceRelationOfYonedaKernelPair isKernelPair).isEquivalenceRelation
        etale_t := by sorry
        etale_s := by sorry }
    atlas_etale := AlgebraicSpace.baseChangePresheafYonedaMap_etale g P.atlas_etale
    atlas_locallySurjective := by sorry
    isKernelPair := isKernelPair }

/-- The presenting scheme of `Presentation.baseChange g P` is `P.U` pulled back to `S`. -/
@[simp]
theorem baseChange_U {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') :
    (P.baseChange g).U = (Over.pullback g).obj P.U := sorry

/-- The relation of `Presentation.baseChange g P` is `P.R` pulled back to `S`. -/
@[simp]
theorem baseChange_R {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') :
    (P.baseChange g).R = P.R.baseChange g := sorry

/-- The atlas of `Presentation.baseChange g P` is the restriction of `P.atlas` along
`Over.map g`, transported by the representable identification. -/
theorem baseChange_atlas {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') :
    (P.baseChange g).atlas =
      (baseChangePresheafYonedaIso g P.U).inv ≫ Functor.whiskerLeft (Over.map g).op P.atlas := sorry

end AlgebraicGeometry.AlgebraicSpace.Presentation
