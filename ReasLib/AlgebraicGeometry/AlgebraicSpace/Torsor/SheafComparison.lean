module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.SheafCategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Category

/-!
# Viewing algebraic-space torsors as sheaf torsors

The comparison 1-morphism of stacks sending an fppf `G_U`-torsor to the
same object viewed as an fppf sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupAlgebraicSpace
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Classifying

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

open Torsors SheafTorsors

/-- A scheme-valued point of the total space of an action `X` over `V → U`. -/
structure RelativePoint {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) (V : Over U.left) where
  /-- The underlying point of the total space of `X`. -/
  val : X.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V))
  /-- The point lies over `V → U`. -/
  over_U :
    X.X.hom.app (op ((Over.map U.hom).obj V)) val =
      yonedaEquiv (ofOverMap (overMapHom V))

/-- Assemble a relative point from an absolute functor-of-points value lying
over `V → U`. -/
def RelativePoint.ofVal {U : Over S} {b : ofOver U ⟶ B}
    {X : Action (baseChange G b)} {V : Over U.left}
    (val : X.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)))
    (over_U :
      X.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V))) :
    RelativePoint G X V where
  val := val
  over_U := over_U

/-- The constructor of `RelativePoint` stores the supplied absolute point and
the over-`U` witness. -/
theorem RelativePoint.ofVal_spec {U : Over S} {b : ofOver U ⟶ B}
    {X : Action (baseChange G b)} {V : Over U.left}
    (val : X.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)))
    (over_U :
      X.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V))) :
    (RelativePoint.ofVal G val over_U).val = val ∧
      (RelativePoint.ofVal G val over_U).over_U = over_U := sorry

/-- The `Over.homMk` triangle of a relative point is the stored over-`U`
condition. -/
theorem RelativePoint.asOverHom_w {U : Over S} {b : ofOver U ⟶ B}
    {X : Action (baseChange G b)} {V : Over U.left}
    (x : RelativePoint G X V) :
    yonedaEquiv.symm x.val ≫ X.X.hom =
      ofOverMap (overMapHom V) := sorry

/-- A relative point of `X` as a morphism over `U`. -/
def RelativePoint.asOverHom {U : Over S} {b : ofOver U ⟶ B}
    {X : Action (baseChange G b)} {V : Over U.left}
    (x : RelativePoint G X V) :
    Over.mk (ofOverMap (overMapHom V)) ⟶ X.X :=
  Over.homMk (yonedaEquiv.symm x.val) (RelativePoint.asOverHom_w G x)

/-- Restriction of a relative point along a morphism of schemes over `U`. -/
def RelativePoint.res {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) {V W : Over U.left} (f : W ⟶ V)
    (x : RelativePoint G X V) : RelativePoint G X W where
  val := X.X.left.functorOfPoints.map ((Over.map U.hom).map f).op x.val
  over_U := sorry

/-- The Type-valued presheaf of relative points of `X` on `(Sch/U)_fppf`. -/
def relativePointPresheaf {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) : (Over U.left)ᵒᵖ ⥤ Type u where
  obj V := RelativePoint G X V.unop
  map {V W} f := TypeCat.ofHom (RelativePoint.res G X f.unop)
  map_id := sorry
  map_comp := sorry

/-- The value of `relativePointPresheaf` on `V` is the type of relative points
over `V`. -/
theorem relativePointPresheaf_obj {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) (V : (Over U.left)ᵒᵖ) :
    (relativePointPresheaf G X).obj V = RelativePoint G X V.unop := sorry

/-- The presheaf of relative points of an algebraic-space action is an fppf
sheaf on `(Sch/U)_fppf`. -/
theorem relativePointPresheaf_isSheaf {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over U.left)
      (relativePointPresheaf G X) := sorry

/-- The fppf sheaf of relative points of `X` on `(Sch/U)_fppf`. -/
def relativePointSheaf {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) :
    Sheaf (Scheme.fppfTopology.over U.left) (Type u) where
  obj := relativePointPresheaf G X
  property := relativePointPresheaf_isSheaf G X

/-- The underlying presheaf of `relativePointSheaf` is
`relativePointPresheaf`. -/
theorem relativePointSheaf_obj {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) :
    (relativePointSheaf G X).obj = relativePointPresheaf G X := sorry

/-- Sections of `relativePointSheaf` over `V` are relative points of `X`
over `V → U`. -/
theorem relativePointSheaf_obj_obj {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) (V : Over U.left) :
    (relativePointSheaf G X).obj.obj (op V) = RelativePoint G X V := sorry

/-- A fibre point of `G` over `b` as a morphism into the pulled-back group `G_U`. -/
def asPullbackGroupHom {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (gp : SheafTorsors.FiberPoint G b V) :
    Over.mk (ofOverMap (overMapHom V)) ⟶ (baseChange G b).X :=
  Over.homMk
    (Limits.pullback.lift (C := AlgebraicSpace S) (f := G.X.hom) (g := b) (yonedaEquiv.symm gp.val)
      (ofOverMap (overMapHom V)) sorry)
    sorry

/-- The action of a fibre point of `G_U` on a relative point of an
algebraic-space torsor. -/
def toSheafTorsorSMul {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) (V : Over U.left)
    (gp : SheafTorsors.FiberPoint G b V) (x : RelativePoint G X V) :
    RelativePoint G X V where
  val :=
    yonedaEquiv
      ((lift (asPullbackGroupHom G gp) (RelativePoint.asOverHom G x) ≫
        X.mod.smul).left)
  over_U := sorry

/-- Identity-action law for the sheaf-level action. -/
theorem toSheafTorsorSMul_one {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) (V : Over U.left)
    (x : RelativePoint G X V) :
    toSheafTorsorSMul G X V 1 x = x := sorry

/-- Compatibility of the sheaf-level action with multiplication in `G`. -/
theorem toSheafTorsorSMul_mul {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) (V : Over U.left)
    (gp gp' : SheafTorsors.FiberPoint G b V) (x : RelativePoint G X V) :
    toSheafTorsorSMul G X V (gp * gp') x =
      toSheafTorsorSMul G X V gp (toSheafTorsorSMul G X V gp' x) := sorry

/-- The `MulAction` of `U ×_{b,ℬ} 𝒢` on the relative points of `X`. -/
@[implicit_reducible]
def toSheafTorsorMulAction {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) (V : Over U.left) :
    MulAction ((baseChangeGroupSheaf G b).obj.obj (op V))
      ((relativePointSheaf G X).obj.obj (op V)) where
  smul := toSheafTorsorSMul G X V
  one_smul := toSheafTorsorSMul_one G X V
  mul_smul := toSheafTorsorSMul_mul G X V

/-- Naturality of the sheaf-level action for restriction maps. -/
theorem toSheafTorsor_act_naturality {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b)) {V W : Over U.left} (f : W ⟶ V)
    (gp : (baseChangeGroupSheaf G b).obj.obj (op V))
    (x : (relativePointSheaf G X).obj.obj (op V)) :
    (relativePointSheaf G X).obj.map f.op (toSheafTorsorSMul G X V gp x) =
      toSheafTorsorSMul G X W ((baseChangeGroupSheaf G b).obj.map f.op gp)
        ((relativePointSheaf G X).obj.map f.op x) := sorry

/-- The sheaf-level action of an fppf `G_U`-torsor is pretransitive. -/
theorem toSheafTorsor_isPretransitive {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b))
    (hX : IsStandardTorsor (baseChange G b) X .fppf) (V : Over U.left) :
    @MulAction.IsPretransitive _ _
      (toSheafTorsorMulAction G X V).toSMul := sorry

/-- The sheaf-level action of an fppf `G_U`-torsor is free. -/
theorem toSheafTorsor_isCancelSMul {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b))
    (hX : IsStandardTorsor (baseChange G b) X .fppf) (V : Over U.left) :
    @IsCancelSMul _ _ (toSheafTorsorMulAction G X V).toSMul := sorry

/-- The sheaf of relative points of an fppf torsor is locally nonempty. -/
theorem toSheafTorsor_locallyNonempty {U : Over S} {b : ofOver U ⟶ B}
    (X : Action (baseChange G b))
    (hX : IsStandardTorsor (baseChange G b) X .fppf) (V : Over U.left) :
    ∃ 𝒮 : Sieve V, 𝒮 ∈ Scheme.fppfTopology.over U.left V ∧
      ∀ ⦃W : Over U.left⦄ (f : W ⟶ V), 𝒮 f →
        Nonempty ((relativePointSheaf G X).obj.obj (op W)) := sorry

/-- View an algebraic-space fppf `G_U`-torsor as a sheaf torsor under
`U ×_{b,ℬ} 𝒢`. -/
def toSheafTorsor {U : Over S} {b : ofOver U ⟶ B}
    {X : Action (baseChange G b)}
    (hX : IsStandardTorsor (baseChange G b) X .fppf) :
    Sheaf.Torsor (baseChangeGroupSheaf G b) where
  carrier := relativePointSheaf G X
  mulAction := toSheafTorsorMulAction G X
  act_naturality := toSheafTorsor_act_naturality G X
  isPretransitive := toSheafTorsor_isPretransitive G X hX
  isCancelSMul := toSheafTorsor_isCancelSMul G X hX
  locallyNonempty := toSheafTorsor_locallyNonempty G X hX

/-- The carrier of `toSheafTorsor` is the sheaf of relative points of `X`
on `(Sch/U)_fppf`. -/
theorem toSheafTorsor_carrier {U : Over S} {b : ofOver U ⟶ B}
    {X : Action (baseChange G b)}
    (hX : IsStandardTorsor (baseChange G b) X .fppf) :
    (toSheafTorsor G hX).carrier = relativePointSheaf G X := sorry

/-- Sections of `toSheafTorsor` over `V` are relative points of `X` over
`V → U`. -/
theorem toSheafTorsor_obj {U : Over S} {b : ofOver U ⟶ B}
    {X : Action (baseChange G b)}
    (hX : IsStandardTorsor (baseChange G b) X .fppf) (V : Over U.left) :
    (toSheafTorsor G hX).carrier.obj.obj (op V) = RelativePoint G X V := sorry

/-- Send an object of `G`-Torsors to the corresponding object of `𝒢/ℬ`-Torsors. -/
def functorObj (ξ : Torsors.Obj G) : SheafTorsors.Obj G where
  U := ξ.U
  b := ξ.b
  P := toSheafTorsor G ξ.isTorsor

/-- The comparison functor preserves the underlying scheme and the morphism to `B`. -/
theorem functorObj_spec (ξ : Torsors.Obj G) :
    (functorObj G ξ).U = ξ.U ∧ (functorObj G ξ).b = ξ.b ∧
      (functorObj G ξ).P = toSheafTorsor G ξ.isTorsor := sorry

/-- Inverse image of the relative-point sheaf along `f : U ⟶ U'` has sections
the relative points over `V → U → U'`. -/
theorem inverseImage_relativePointSheaf_obj {U U' : Over S} (f : U ⟶ U')
    {b' : ofOver U' ⟶ B} (X : Action (baseChange G b'))
    (V : (Over U.left)ᵒᵖ) :
    ((AlgebraicGeometry.SheafTorsors.inverseImage f).obj (relativePointSheaf G X)).obj.obj V =
      RelativePoint G X ((Over.map f.left).obj V.unop) := sorry

/-- Transport a relative point of `ξ` along a morphism of `G`-Torsors. -/
def functorMapRelativePoint {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ')
    (V : Over ξ.U.left) (x : RelativePoint G ξ.X V) :
    RelativePoint G ξ'.X ((Over.map α.f.left).obj V) where
  val :=
    ξ'.X.X.left.functorOfPoints.map (baseOverIso α.f V).symm.hom.op
      ((Limits.pullback.fst (C := AlgebraicSpace S) ξ'.X.X.hom (ofOverMap α.f)).app
        (op ((Over.map ξ.U.hom).obj V))
        (α.g.hom.left.app (op ((Over.map ξ.U.hom).obj V)) x.val))
  over_U := sorry

/-- Transport a relative point of `ξ'` back along a morphism of `G`-Torsors. -/
def functorMapRelativePointInv {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ')
    (V : Over ξ.U.left) (x : RelativePoint G ξ'.X ((Over.map α.f.left).obj V)) :
    RelativePoint G ξ.X V where
  val :=
    α.g.inv.left.app (op ((Over.map ξ.U.hom).obj V))
      (yonedaEquiv
        (Limits.pullback.lift (C := AlgebraicSpace S)
          (yonedaEquiv.symm
            (ξ'.X.X.left.functorOfPoints.map (baseOverIso α.f V).hom.op x.val))
          (ofOverMap (overMapHom V))
          (by sorry)))
  over_U := sorry

/-- Component of the comparison sheaf map on relative-point sections. -/
def functorMapCarrierHomApp {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ')
    (V : (Over ξ.U.left)ᵒᵖ) :
    (functorObj G ξ).P.carrier.obj.obj V ⟶
      ((AlgebraicGeometry.SheafTorsors.inverseImage α.f).obj (functorObj G ξ').P.carrier).obj.obj V :=
  TypeCat.ofHom fun x ↦ functorMapRelativePoint G α V.unop x

/-- `functorMapCarrierHomApp` is transport of relative points along `α`. -/
theorem functorMapCarrierHomApp_apply {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ')
    (V : (Over ξ.U.left)ᵒᵖ) (x : RelativePoint G ξ.X V.unop) :
    functorMapCarrierHomApp G α V x = functorMapRelativePoint G α V.unop x := sorry

/-- Component of the inverse comparison sheaf map on relative-point sections. -/
def functorMapCarrierInvApp {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ')
    (V : (Over ξ.U.left)ᵒᵖ) :
    ((AlgebraicGeometry.SheafTorsors.inverseImage α.f).obj (functorObj G ξ').P.carrier).obj.obj V ⟶
      (functorObj G ξ).P.carrier.obj.obj V :=
  TypeCat.ofHom fun x ↦ functorMapRelativePointInv G α V.unop x

/-- `functorMapCarrierInvApp` is inverse transport of relative points along `α`. -/
theorem functorMapCarrierInvApp_apply {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ')
    (V : (Over ξ.U.left)ᵒᵖ)
    (x : RelativePoint G ξ'.X ((Over.map α.f.left).obj V.unop)) :
    functorMapCarrierInvApp G α V x = functorMapRelativePointInv G α V.unop x := sorry

/-- The sheaf map on carriers induced by an isomorphism of algebraic-space torsors. -/
def functorMapCarrierHom {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ') :
    (functorObj G ξ).P.carrier ⟶
      (AlgebraicGeometry.SheafTorsors.inverseImage α.f).obj (functorObj G ξ').P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun V ↦ functorMapCarrierHomApp G α V
      naturality := sorry }

/-- The inverse sheaf map on carriers induced by an isomorphism of algebraic-space torsors. -/
def functorMapCarrierInv {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ') :
    (AlgebraicGeometry.SheafTorsors.inverseImage α.f).obj (functorObj G ξ').P.carrier ⟶
      (functorObj G ξ).P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun V ↦ functorMapCarrierInvApp G α V
      naturality := sorry }

/-- The carrier isomorphism `f⁻¹𝒳' ≅ 𝒳` associated to a morphism of
algebraic-space torsors. -/
def functorMapCarrierIso {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ') :
    (AlgebraicGeometry.SheafTorsors.inverseImage α.f).obj (functorObj G ξ').P.carrier ≅
      (functorObj G ξ).P.carrier where
  hom := functorMapCarrierInv G α
  inv := functorMapCarrierHom G α
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The carrier isomorphism of the comparison functor is equivariant. -/
theorem functorMap_equivariant {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ') :
    SheafTorsors.IsEquivariant G (functorObj G ξ) (functorObj G ξ') α.f α.comm
      (functorMapCarrierIso G α) := sorry

/-- Send a morphism of `G`-Torsors to the corresponding morphism of `𝒢/ℬ`-Torsors. -/
def functorMap {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ') :
    SheafTorsors.Hom (functorObj G ξ) (functorObj G ξ') where
  f := α.f
  comm := α.comm
  g := functorMapCarrierIso G α
  equivariant := functorMap_equivariant G α

/-- The comparison functor on objects of `G`-Torsors and `𝒢/ℬ`-Torsors. -/
def functor : Torsors.Obj G ⥤ SheafTorsors.Obj G where
  obj ξ := functorObj G ξ
  map α := functorMap G α
  map_id := sorry
  map_comp := sorry

/-- The comparison functor sends `(U, b, X)` to `(U, b, toSheafTorsor X)`. -/
theorem functor_obj (ξ : Torsors.Obj G) :
    (functor G).obj ξ = functorObj G ξ := sorry

/-- The comparison functor lies over `(Sch/S)_fppf`. -/
theorem basedFunctor_w : functor G ⋙ SheafTorsors.forget G = Torsors.forget G := sorry

/-- The based comparison functor of classifying stacks over `(Sch/S)_fppf`. -/
def basedFunctor :
    (Torsors.stack G).toBasedCategory ⥤ᵇ (SheafTorsors.stack G).toBasedCategory where
  toFunctor := functor G
  w := basedFunctor_w G

/-- The comparison 1-morphism of stacks `G`-Torsors ⟶ `𝒢/ℬ`-Torsors. -/
def toSheafHom : Torsors.stack G ⟶ SheafTorsors.stack G :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (basedFunctor G))

/-- The comparison 1-morphism is the lift of `basedFunctor`. -/
theorem toSheafHom_eq :
    toSheafHom G =
      StackOver.Groupoids.Hom.lift
        (FiberedCategoryOver.Groupoids.ofBasedFunctor (basedFunctor G)) := sorry

/-- Viewing an fppf torsor under a group algebraic space as its sheaf of relative
points gives an equivalence of stacks in groupoids over the fppf site. -/
instance toSheafHom_isEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    CategoryTheory.BasedFunctor.IsEquivalence (basedFunctor G) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Classifying
