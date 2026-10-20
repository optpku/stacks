module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.SheafTorsor.Restriction

/-!
# Group objects in the slice of fppf sheaves

A group object of `Sh((Sch/S)_fppf)/ℬ` is an internal group in `Over ℬ`. Fibrewise
sections of `U ×_{b,ℬ} 𝒢` are points of `𝒢` over `V → U` lying over `b|_V`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CartesianMonoidalCategory
open AlgebraicGeometry.SheafTorsors (inverseImageGrp)
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.SheafTorsorsOver

/-- The slice of fppf sheaves over `ℬ` carries its canonical Cartesian monoidal
structure, given by fibre products over `ℬ`. -/
noncomputable instance instCartesianMonoidalCategoryOver
    {S : Scheme.{u}} (ℬ : Sheaf (Scheme.fppfTopology.over S) (Type u)) :
    CartesianMonoidalCategory (Over ℬ) :=
  Over.cartesianMonoidalCategory ℬ

variable {S : Scheme.{u}} {ℬ : Sheaf (Scheme.fppfTopology.over S) (Type u)}

/-- The morphism `(Over.map U.hom).obj V ⟶ U` induced by the structure map of `V`. -/
def overMapHom {U : Over S} (V : Over U.left) :
    (Over.map U.hom).obj V ⟶ U :=
  Over.homMk V.hom rfl

/-- The sheaf morphism `y(V) ⟶ ℬ` obtained by restricting the section `b` along
`V → U`. -/
def restrictSection {U : Over S} (b : ℬ.obj.obj (op U)) (V : Over U.left) :
    (Scheme.fppfTopology.over S).yoneda.obj ((Over.map U.hom).obj V) ⟶ ℬ :=
  (Scheme.fppfTopology.over S).yonedaEquiv.symm (ℬ.obj.map (overMapHom V).op b)

/-- Composing `V → U → S` or `V → U → U' → S` yields the same object of `Over S`. -/
def baseOverIso {U U' : Over S} (f : U ⟶ U') (V : Over U.left) :
    (Over.map U.hom).obj V ≅ (Over.map U'.hom).obj ((Over.map f.left).obj V) :=
  Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans
      ((Category.assoc V.hom f.left U'.hom).trans
        (congrArg (fun t ↦ V.hom ≫ t) (Over.w f))))

variable (𝒢 : Grp (Over ℬ))

/-- A scheme-valued point of `𝒢` over `V → U` lying over the section `b` of `ℬ`. -/
structure FiberPoint {U : Over S} (b : ℬ.obj.obj (op U)) (V : Over U.left) where
  /-- The underlying section of the total sheaf of `𝒢`. -/
  val : 𝒢.X.left.obj.obj (op ((Over.map U.hom).obj V))
  /-- The point lies over `b` restricted to `V`. -/
  over_b :
    𝒢.X.hom.hom.app (op ((Over.map U.hom).obj V)) val =
      ℬ.obj.map (overMapHom V).op b

/-- The morphism `y(V) ⟶ 𝒢` over `ℬ` associated to a fibre point. -/
def FiberPoint.asOverHom {U : Over S} {b : ℬ.obj.obj (op U)} {V : Over U.left}
    (x : FiberPoint 𝒢 b V) :
    Over.mk (restrictSection b V) ⟶ 𝒢.X :=
  Over.homMk ((Scheme.fppfTopology.over S).yonedaEquiv.symm x.val) sorry

/-- Multiplication of fibre points uses the multiplication of `𝒢`. -/
def FiberPoint.mul {U : Over S} {b : ℬ.obj.obj (op U)} {V : Over U.left}
    (x y : FiberPoint 𝒢 b V) : FiberPoint 𝒢 b V where
  val :=
    (Scheme.fppfTopology.over S).yonedaEquiv
      ((lift x.asOverHom y.asOverHom).left ≫ μ[𝒢.X].left)
  over_b := sorry

/-- The identity fibre point is the unit of `𝒢` pulled back along `b`. -/
def FiberPoint.one {U : Over S} {b : ℬ.obj.obj (op U)} (V : Over U.left) :
    FiberPoint 𝒢 b V where
  val :=
    (Scheme.fppfTopology.over S).yonedaEquiv
      ((toUnit (Over.mk (restrictSection b V))).left ≫ η[𝒢.X].left)
  over_b := sorry

/-- Inversion of fibre points uses the inverse of `𝒢`. -/
def FiberPoint.inv {U : Over S} {b : ℬ.obj.obj (op U)} {V : Over U.left}
    (x : FiberPoint 𝒢 b V) : FiberPoint 𝒢 b V where
  val :=
    (Scheme.fppfTopology.over S).yonedaEquiv (x.asOverHom.left ≫ ι[𝒢.X].left)
  over_b := sorry

/-- Multiplication of fibre points is associative. -/
theorem FiberPoint.mul_assoc {U : Over S} {b : ℬ.obj.obj (op U)} {V : Over U.left}
    (x y z : FiberPoint 𝒢 b V) :
    FiberPoint.mul 𝒢 (FiberPoint.mul 𝒢 x y) z =
      FiberPoint.mul 𝒢 x (FiberPoint.mul 𝒢 y z) := sorry

/-- Left unit law for fibre points. -/
theorem FiberPoint.one_mul {U : Over S} {b : ℬ.obj.obj (op U)} {V : Over U.left}
    (x : FiberPoint 𝒢 b V) :
    FiberPoint.mul 𝒢 (FiberPoint.one 𝒢 V) x = x := sorry

/-- Right unit law for fibre points. -/
theorem FiberPoint.mul_one {U : Over S} {b : ℬ.obj.obj (op U)} {V : Over U.left}
    (x : FiberPoint 𝒢 b V) :
    FiberPoint.mul 𝒢 x (FiberPoint.one 𝒢 V) = x := sorry

/-- Left inverse law for fibre points. -/
theorem FiberPoint.inv_mul_cancel {U : Over S} {b : ℬ.obj.obj (op U)} {V : Over U.left}
    (x : FiberPoint 𝒢 b V) :
    FiberPoint.mul 𝒢 (FiberPoint.inv 𝒢 x) x = FiberPoint.one 𝒢 V := sorry

/-- The bundled group of fibre points of `𝒢` over `b`, with its internal group operations. -/
def fiberPointGroup {U : Over S} (b : ℬ.obj.obj (op U)) (V : Over U.left) :
    GrpCat.{u} where
  carrier := FiberPoint 𝒢 b V
  str :=
    { mul := FiberPoint.mul 𝒢
      one := FiberPoint.one 𝒢 V
      inv := FiberPoint.inv 𝒢
      mul_assoc := FiberPoint.mul_assoc 𝒢
      one_mul := FiberPoint.one_mul 𝒢
      mul_one := FiberPoint.mul_one 𝒢
      inv_mul_cancel := FiberPoint.inv_mul_cancel 𝒢 }

/-- Restriction of a fibre point along a morphism of schemes over `U`. -/
def FiberPoint.res {U : Over S} {b : ℬ.obj.obj (op U)} {V W : Over U.left} (f : W ⟶ V)
    (x : FiberPoint 𝒢 b V) : FiberPoint 𝒢 b W where
  val := 𝒢.X.left.obj.map ((Over.map U.hom).map f).op x.val
  over_b := sorry

/-- Restriction of fibre points is a group homomorphism. -/
def FiberPoint.resHom {U : Over S} {b : ℬ.obj.obj (op U)} {V W : Over U.left} (f : W ⟶ V) :
    fiberPointGroup 𝒢 b V →* fiberPointGroup 𝒢 b W where
  toFun := FiberPoint.res 𝒢 f
  map_one' := sorry
  map_mul' := sorry

/-- The group-valued presheaf of points of `U ×_{b,ℬ} 𝒢`. -/
def baseChangePresheaf {U : Over S} (b : ℬ.obj.obj (op U)) :
    (Over U.left)ᵒᵖ ⥤ GrpCat.{u} where
  obj V := fiberPointGroup 𝒢 b V.unop
  map {V W} f := ConcreteCategory.ofHom (C := GrpCat) (FiberPoint.resHom 𝒢 f.unop)
  map_id := sorry
  map_comp := sorry

/-- The group-valued presheaf of points of `U ×_{b,ℬ} 𝒢` is an fppf sheaf. -/
theorem baseChangePresheaf_isSheaf {U : Over S} (b : ℬ.obj.obj (op U)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over U.left) (baseChangePresheaf 𝒢 b) := sorry

/-- The fppf sheaf of groups `U ×_{b,ℬ} 𝒢` on `(Sch/U)_fppf`. -/
def baseChangeGroupSheaf {U : Over S} (b : ℬ.obj.obj (op U)) :
    Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} where
  obj := baseChangePresheaf 𝒢 b
  property := baseChangePresheaf_isSheaf 𝒢 b

/-- The underlying group-valued presheaf of `baseChangeGroupSheaf` is
`baseChangePresheaf`. -/
theorem baseChangeGroupSheaf_obj {U : Over S} (b : ℬ.obj.obj (op U)) :
    (baseChangeGroupSheaf 𝒢 b).obj = baseChangePresheaf 𝒢 b := rfl

/-- Group sections of `U ×_{b,ℬ} 𝒢` and of `U' ×_{b',ℬ} 𝒢` agree after inverse
image along `f`. -/
def groupMulEquiv {U U' : Over S} (f : U ⟶ U') (b' : ℬ.obj.obj (op U'))
    (V : Over U.left) :
    fiberPointGroup 𝒢 (ℬ.obj.map f.op b') V ≃*
      fiberPointGroup 𝒢 b' ((Over.map f.left).obj V) where
  toEquiv :=
    { toFun x :=
        { val := 𝒢.X.left.obj.map (baseOverIso f V).symm.hom.op x.val
          over_b := sorry }
      invFun x :=
        { val := 𝒢.X.left.obj.map (baseOverIso f V).hom.op x.val
          over_b := sorry }
      left_inv := sorry
      right_inv := sorry }
  map_mul' := sorry

/-- Transport a fibre point along an equality of sections of `ℬ`. -/
def FiberPoint.transport {U : Over S} {b b' : ℬ.obj.obj (op U)} (h : b = b')
    {V : Over U.left} (x : FiberPoint 𝒢 b V) : FiberPoint 𝒢 b' V :=
  h ▸ x

/-- Inverse image of the underlying group-valued presheaf of
`U' ×_{b',ℬ} 𝒢` along `f : U ⟶ U'` is the presheaf of
`U ×_{b'∘f,ℬ} 𝒢`. -/
def baseChangeIso_presheaf {U U' : Over S} (f : U ⟶ U') (b' : ℬ.obj.obj (op U')) :
    ((inverseImageGrp f).obj (baseChangeGroupSheaf 𝒢 b')).obj ≅
      (baseChangeGroupSheaf 𝒢 (ℬ.obj.map f.op b')).obj where
  hom :=
    { app := fun V ↦ ConcreteCategory.ofHom (C := GrpCat)
        (groupMulEquiv 𝒢 f b' V.unop).symm.toMonoidHom
      naturality := sorry }
  inv :=
    { app := fun V ↦ ConcreteCategory.ofHom (C := GrpCat)
        (groupMulEquiv 𝒢 f b' V.unop).toMonoidHom
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse image of `U' ×_{b',ℬ} 𝒢` along `f : U ⟶ U'` is
`U ×_{b'∘f,ℬ} 𝒢`. -/
def baseChangeIso {U U' : Over S} (f : U ⟶ U') (b' : ℬ.obj.obj (op U')) :
    (inverseImageGrp f).obj (baseChangeGroupSheaf 𝒢 b') ≅
      baseChangeGroupSheaf 𝒢 (ℬ.obj.map f.op b') where
  hom := Sheaf.homEquiv.symm (baseChangeIso_presheaf 𝒢 f b').hom
  inv := Sheaf.homEquiv.symm (baseChangeIso_presheaf 𝒢 f b').inv
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.SheafTorsorsOver
