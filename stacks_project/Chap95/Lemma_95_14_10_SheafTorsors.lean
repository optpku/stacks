module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import ReasLib.CategoryTheory.Sites.Torsor.Basic
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Definition_78_5_1_Group

/-!
# Relative sheaf torsors for a group algebraic space

The stack in groupoids of `𝒢/ℬ`-torsors, where `𝒢` and `ℬ` are a group
algebraic space `G` over `B` viewed as fppf sheaves on `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/-- The morphism `(Over.map U.hom).obj V ⟶ U` induced by the structure map of `V`. -/
def overMapHom {U : Over S} (V : Over U.left) :
    (Over.map U.hom).obj V ⟶ U :=
  Over.homMk V.hom rfl

/-- Restriction of an fppf sheaf of types from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrict (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map U.hom).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image of an fppf sheaf of types along a morphism in `Over S`. -/
def inverseImage {U U' : Over S} (f : U ⟶ U') :
    Sheaf (Scheme.fppfTopology.over U'.left) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map f.left).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)

/-- Inverse image along an identity morphism of `Over S` is the identity functor. -/
def inverseImageId (U : Over S) :
    inverseImage (𝟙 U) ≅ 𝟭 (Sheaf (Scheme.fppfTopology.over U.left) (Type u)) :=
  Functor.sheafPushforwardContinuousId' (Over.mapId U.left) (Type u)
    (Scheme.fppfTopology.over U.left)

/-- Inverse image is contravariant for composition in `Over S`. -/
def inverseImageComp {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'') :
    inverseImage g ⋙ inverseImage f ≅ inverseImage (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f.left g.left).symm (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over U''.left)

/-- Restricting from `S` to `U'` and then pulling back along `f : U ⟶ U'` is
restriction to `U`. -/
def restrictIso {U U' : Over S} (f : U ⟶ U') :
    restrict U' ⋙ inverseImage f ≅ restrict U :=
  Functor.sheafPushforwardContinuousComp'
    ((Over.mapComp f.left U'.hom).symm ≪≫ Over.mapCongr (f.left ≫ U'.hom) U.hom f.w)
    (Type u) (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over S)

/-- Composing `V → U → S` or `V → U → U' → S` yields the same object of `Over S`. -/
def baseOverIso {U U' : Over S} (f : U ⟶ U') (V : Over U.left) :
    (Over.map U.hom).obj V ≅ (Over.map U'.hom).obj ((Over.map f.left).obj V) :=
  Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans
      ((Category.assoc V.hom f.left U'.hom).trans
        (congrArg (fun t ↦ V.hom ≫ t) (Over.w f))))

/-- A scheme-valued point of `G` over `V → U` lying over `b : U ⟶ B`. -/
structure FiberPoint {U : Over S} (b : ofOver U ⟶ B) (V : Over U.left) where
  /-- The underlying point of the total space of `G`. -/
  val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V))
  /-- The point lies over `b` restricted to `V`. -/
  over_b :
    G.X.hom.app (op ((Over.map U.hom).obj V)) val =
      yonedaEquiv (ofOverMap (overMapHom V) ≫ b)

/-- The morphism `ofOver V ⟶ G` over `B` associated to a fibre point. -/
def FiberPoint.asOverHom {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : FiberPoint G b V) :
    Over.mk (ofOverMap (overMapHom V) ≫ b) ⟶ G.X :=
  Over.homMk (yonedaEquiv.symm x.val) sorry

/-- Multiplication of fibre points uses the multiplication of `G`. -/
def FiberPoint.mul {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x y : FiberPoint G b V) : FiberPoint G b V where
  val := yonedaEquiv ((lift x.asOverHom y.asOverHom).left ≫ μ[G.X].left)
  over_b := sorry

/-- The identity fibre point is the unit of `G` pulled back along `b`. -/
def FiberPoint.one {U : Over S} {b : ofOver U ⟶ B} (V : Over U.left) :
    FiberPoint G b V where
  val :=
    yonedaEquiv
      ((toUnit (Over.mk (ofOverMap (overMapHom V) ≫ b))).left ≫ η[G.X].left)
  over_b := sorry

/-- Inversion of fibre points uses the inverse of `G`. -/
def FiberPoint.inv {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : FiberPoint G b V) : FiberPoint G b V where
  val := yonedaEquiv (x.asOverHom.left ≫ ι[G.X].left)
  over_b := sorry

/-- Associativity of multiplication of fibre points. -/
theorem FiberPoint.mul_assoc {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x y z : FiberPoint G b V) :
    FiberPoint.mul G (FiberPoint.mul G x y) z =
      FiberPoint.mul G x (FiberPoint.mul G y z) := sorry

/-- Left unit law for fibre points. -/
theorem FiberPoint.one_mul {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : FiberPoint G b V) :
    FiberPoint.mul G (FiberPoint.one G V) x = x := sorry

/-- Right unit law for fibre points. -/
theorem FiberPoint.mul_one {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : FiberPoint G b V) :
    FiberPoint.mul G x (FiberPoint.one G V) = x := sorry

/-- Left inverse law for fibre points. -/
theorem FiberPoint.inv_mul_cancel {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : FiberPoint G b V) :
    FiberPoint.mul G (FiberPoint.inv G x) x = FiberPoint.one G V := sorry

/-- Fibre points of `G` over `b` form a group. -/
instance instGroup_fiberPoint {U : Over S} (b : ofOver U ⟶ B) (V : Over U.left) :
    Group (FiberPoint G b V) where
  mul := FiberPoint.mul G
  one := FiberPoint.one G V
  inv := FiberPoint.inv G
  mul_assoc := FiberPoint.mul_assoc G
  one_mul := FiberPoint.one_mul G
  mul_one := FiberPoint.mul_one G
  inv_mul_cancel := FiberPoint.inv_mul_cancel G

/-- Restriction of a fibre point along a morphism of schemes over `U`. -/
def FiberPoint.res {U : Over S} {b : ofOver U ⟶ B} {V W : Over U.left} (f : W ⟶ V)
    (x : FiberPoint G b V) : FiberPoint G b W where
  val := G.X.left.functorOfPoints.map ((Over.map U.hom).map f).op x.val
  over_b := sorry

/-- Restriction of fibre points is a group homomorphism. -/
def FiberPoint.resHom {U : Over S} {b : ofOver U ⟶ B} {V W : Over U.left} (f : W ⟶ V) :
    FiberPoint G b V →* FiberPoint G b W where
  toFun := FiberPoint.res G f
  map_one' := sorry
  map_mul' := sorry

/-- The group-valued presheaf of points of `U ×_{b,ℬ} 𝒢`. -/
def baseChangePresheaf {U : Over S} (b : ofOver U ⟶ B) :
    (Over U.left)ᵒᵖ ⥤ GrpCat.{u} where
  obj V := GrpCat.of (FiberPoint G b V.unop)
  map {V W} f := GrpCat.ofHom (FiberPoint.resHom G f.unop)
  map_id := sorry
  map_comp := sorry

/-- The group-valued presheaf of points of `U ×_{b,ℬ} 𝒢` is an fppf sheaf. -/
theorem baseChangePresheaf_isSheaf {U : Over S} (b : ofOver U ⟶ B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over U.left) (baseChangePresheaf G b) := sorry

/-- The fppf sheaf of groups `U ×_{b,ℬ} 𝒢` on `(Sch/U)_fppf`. -/
def baseChangeGroupSheaf {U : Over S} (b : ofOver U ⟶ B) :
    Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} where
  obj := baseChangePresheaf G b
  property := baseChangePresheaf_isSheaf G b

/-- The underlying group-valued presheaf of `baseChangeGroupSheaf` is
`baseChangePresheaf`. -/
theorem baseChangeGroupSheaf_obj {U : Over S} (b : ofOver U ⟶ B) :
    (baseChangeGroupSheaf G b).obj = baseChangePresheaf G b := sorry

/-- An object of `𝒢/ℬ`-Torsors: a scheme `U` over `S`, a section of `ℬ` over `U`,
and a torsor under `U ×_{b,ℬ} 𝒢`. -/
structure Obj (G : GroupAlgebraicSpace B) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The section of `ℬ` over `U`. -/
  b : ofOver U ⟶ B
  /-- The sheaf torsor under `U ×_{b,ℬ} 𝒢`. -/
  P : Sheaf.Torsor (baseChangeGroupSheaf G b)

/-- Assemble an object of `𝒢/ℬ`-Torsors from a scheme, a section of `ℬ`, and a
sheaf torsor. -/
def ofTorsor (U : Over S) (b : ofOver U ⟶ B)
    (P : Sheaf.Torsor (baseChangeGroupSheaf G b)) : Obj G where
  U := U
  b := b
  P := P

/-- The constructor of `Obj` stores the supplied scheme, section, and torsor. -/
theorem ofTorsor_spec (U : Over S) (b : ofOver U ⟶ B)
    (P : Sheaf.Torsor (baseChangeGroupSheaf G b)) :
    (ofTorsor G U b P).U = U ∧ (ofTorsor G U b P).b = b ∧
      (ofTorsor G U b P).P = P := sorry

/-- Group sections of `U ×_{b,ℬ} 𝒢` and of `U' ×_{b',ℬ} 𝒢` agree after inverse
image along `f`. -/
def groupMulEquiv {U U' : Over S} (f : U ⟶ U') (b' : ofOver U' ⟶ B)
    (V : Over U.left) :
    FiberPoint G (ofOverMap f ≫ b') V ≃*
      FiberPoint G b' ((Over.map f.left).obj V) where
  toEquiv :=
    { toFun x :=
        { val := G.X.left.functorOfPoints.map (baseOverIso f V).symm.hom.op x.val
          over_b := sorry }
      invFun x :=
        { val := G.X.left.functorOfPoints.map (baseOverIso f V).hom.op x.val
          over_b := sorry }
      left_inv := sorry
      right_inv := sorry }
  map_mul' := sorry

/-- Transport a fibre point along an equality of morphisms to `B`. -/
def FiberPoint.transport {U : Over S} {b b' : ofOver U ⟶ B} (h : b = b')
    {V : Over U.left} (x : FiberPoint G b V) : FiberPoint G b' V :=
  h ▸ x

/-- A carrier isomorphism over `f` is equivariant if it intertwines the
`𝒢`-actions after identifying group sections along inverse image. -/
def IsEquivariant (ξ ξ' : Obj G) (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier) : Prop :=
  ∀ (V : Over ξ.U.left)
    (gp : FiberPoint G ξ.b V)
    (x : ((inverseImage f).obj ξ'.P.carrier).obj.obj (op V)),
    g.hom.hom.app (op V)
        ((ξ'.P.mulAction ((Over.map f.left).obj V)).smul
          (groupMulEquiv G f ξ'.b V (FiberPoint.transport G h gp)) x) =
      (ξ.P.mulAction V).smul gp (g.hom.hom.app (op V) x)

/-- A morphism of `𝒢/ℬ`-Torsors: a map of schemes over `B` and an equivariant
isomorphism `f⁻¹ℱ' ≅ ℱ` of sheaf torsors. -/
structure Hom {G : GroupAlgebraicSpace B} (ξ ξ' : Obj G) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The morphism `f` lies over `ℬ`. -/
  comm : ξ.b = ofOverMap f ≫ ξ'.b
  /-- The isomorphism `f⁻¹ℱ' ≅ ℱ` of torsor carriers. -/
  g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier
  /-- The isomorphism `g` is equivariant for the group actions. -/
  equivariant : IsEquivariant G ξ ξ' f comm g

/-- Assemble a morphism from a scheme map and an equivariant carrier isomorphism. -/
def ofIso {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U) (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (hg : IsEquivariant G ξ ξ' f h g) : Hom ξ ξ' where
  f := f
  comm := h
  g := g
  equivariant := hg

/-- The constructor of `Hom` stores the supplied scheme map, over-`ℬ` equality,
isomorphism, and equivariance witness. -/
theorem ofIso_spec {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (hg : IsEquivariant G ξ ξ' f h g) :
    (ofIso G f h g hg).f = f ∧ (ofIso G f h g hg).comm = h ∧
      (ofIso G f h g hg).g = g ∧ (ofIso G f h g hg).equivariant = hg := sorry

/-- Identity of schemes over `S` is compatible with the section of `ℬ`. -/
theorem id_comm (ξ : Obj G) : ξ.b = ofOverMap (𝟙 ξ.U) ≫ ξ.b := sorry

/-- The identity comparison of torsor carriers is equivariant. -/
theorem id_equivariant (ξ : Obj G) :
    IsEquivariant G ξ ξ (𝟙 ξ.U) (id_comm G ξ)
      ((inverseImageId ξ.U).app ξ.P.carrier) :=
  sorry

/-- Identity morphisms of `𝒢/ℬ`-Torsors. -/
def idHom (ξ : Obj G) : Hom ξ ξ where
  f := 𝟙 ξ.U
  comm := id_comm G ξ
  g := (inverseImageId ξ.U).app ξ.P.carrier
  equivariant := id_equivariant G ξ

/-- The composite isomorphism of torsor carriers along a composite of scheme maps. -/
def compIso {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (inverseImage (α.f ≫ β.f)).obj ξ''.P.carrier ≅ ξ.P.carrier :=
  (inverseImageComp α.f β.f).symm.app ξ''.P.carrier ≪≫
    (inverseImage α.f).mapIso β.g ≪≫ α.g

/-- Compatibility of a composite morphism with the sections of `ℬ`. -/
theorem comp_comm {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.b = ofOverMap (α.f ≫ β.f) ≫ ξ''.b := sorry

/-- The composite isomorphism of torsor carriers is equivariant. -/
theorem comp_equivariant {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariant G ξ ξ'' (α.f ≫ β.f) (comp_comm G α β) (compIso G α β) := sorry

/-- Composition of morphisms of `𝒢/ℬ`-Torsors. -/
def compHom {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  comm := comp_comm G α β
  g := compIso G α β
  equivariant := comp_equivariant G α β

/-- Left identity law for morphisms of `𝒢/ℬ`-Torsors. -/
theorem idHom_comp {ξ ξ' : Obj G} (α : Hom ξ ξ') : compHom G (idHom G ξ) α = α := sorry

/-- Right identity law for morphisms of `𝒢/ℬ`-Torsors. -/
theorem compHom_id {ξ ξ' : Obj G} (α : Hom ξ ξ') : compHom G α (idHom G ξ') = α := sorry

/-- Associativity of composition of morphisms of `𝒢/ℬ`-Torsors. -/
theorem assocHom {ξ₁ ξ₂ ξ₃ ξ₄ : Obj G} (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (c : Hom ξ₃ ξ₄) :
    compHom G (compHom G α β) c = compHom G α (compHom G β c) := sorry

/-- The category of objects of `𝒢/ℬ`-Torsors. -/
instance instCategory : Category (Obj G) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom G ξ
  comp α β := compHom G α β
  id_comp := idHom_comp G
  comp_id := compHom_id G
  assoc := assocHom G

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id (ξ : Obj G) : (idHom G ξ).f = 𝟙 ξ.U := sorry

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom G α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor from `𝒢/ℬ`-Torsors to `(Sch/S)_fppf`. -/
def forget (G : GroupAlgebraicSpace B) : Obj G ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id G
  map_comp := forget_map_comp G

/-- The forgetful functor sends `(U, b, P)` to `U`. -/
theorem forget_obj (ξ : Obj G) : (forget G).obj ξ = ξ.U := sorry

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ξ ξ' : Obj G} (α : Hom ξ ξ') : (forget G).map α = α.f := sorry

/-- The forgetful functor is fibered in groupoids. -/
instance instIsFiberedInGroupoids : Functor.IsFibered.InGroupoids (forget G) := sorry

/-- The forgetful functor is a stack in groupoids on the big fppf site. -/
instance instIsStackInGroupoids :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget G) := sorry

/-- The stack in groupoids of `𝒢/ℬ`-torsors over `(Sch/S)_fppf`. -/
def stack (G : GroupAlgebraicSpace B) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget G)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p : (stack G).p = forget G := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors
