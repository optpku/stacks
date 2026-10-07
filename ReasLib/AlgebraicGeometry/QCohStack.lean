module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

/-!
# The category of pairs of an `S`-scheme and a quasi-coherent sheaf

Objects of `QCohStack` are pairs `(X, F)` with `X` an `S`-scheme and `F` quasi-coherent on `X`.
A morphism `(Y, G) ⟶ (X, F)` is a morphism `f : Y ⟶ X` over `S` together with a map
`(QCoh.pullback f).obj F ⟶ G` in `QCoh Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.QCohStack

/-- An object of `QCohStack` over `S` is an `S`-scheme together with a quasi-coherent sheaf. -/
def Obj (S : Scheme.{u}) := Σ base : Over S, Scheme.QCoh base.left

/-- The underlying object of `(Sch/S)` associated to an object of `QCohStack`. -/
def Obj.base {S : Scheme.{u}} (x : Obj S) : Over S := x.1

/-- The quasi-coherent sheaf associated to an object of `QCohStack`. -/
def Obj.sheaf {S : Scheme.{u}} (x : Obj S) : Scheme.QCoh x.base.left := x.2

/-- Package an `S`-scheme and a quasi-coherent sheaf as an object of `QCohStack`. -/
def of {S : Scheme.{u}} (X : Over S) (F : Scheme.QCoh X.left) : Obj S :=
  ⟨X, F⟩

/-- The underlying `S`-scheme of `of X F` is `X`. -/
theorem of_base {S : Scheme.{u}} (X : Over S) (F : Scheme.QCoh X.left) :
    (of X F).base = X :=
  sorry

/-- The quasi-coherent sheaf of `of X F` is `F`. -/
theorem of_sheaf {S : Scheme.{u}} (X : Over S) (F : Scheme.QCoh X.left) :
    (of X F).sheaf = F :=
  sorry

/-- A morphism `(Y, G) ⟶ (X, F)` is an `S`-morphism `f : Y ⟶ X` and a map `f* F ⟶ G`. -/
def Hom {S : Scheme.{u}} (x y : Obj S) :=
  Σ base : x.base ⟶ y.base,
    ((Scheme.QCoh.pullback base.left).obj y.sheaf ⟶ x.sheaf)

/-- The underlying `S`-morphism of a `QCohStack` morphism. -/
def Hom.base {S : Scheme.{u}} {x y : Obj S} (α : Hom x y) : x.base ⟶ y.base := α.1

/-- The pullback sheaf map of a `QCohStack` morphism. -/
def Hom.sheaf {S : Scheme.{u}} {x y : Obj S} (α : Hom x y) :
    (Scheme.QCoh.pullback α.base.left).obj y.sheaf ⟶ x.sheaf := α.2

/-- Build a `QCohStack` morphism from an `S`-morphism and a pullback map of sheaves. -/
def homMk {S : Scheme.{u}} {x y : Obj S} (base : x.base ⟶ y.base)
    (sheaf : (Scheme.QCoh.pullback base.left).obj y.sheaf ⟶ x.sheaf) : Hom x y :=
  ⟨base, sheaf⟩

/-- The underlying `S`-morphism of `homMk` is the supplied base map. -/
theorem homMk_base {S : Scheme.{u}} {x y : Obj S} (base : x.base ⟶ y.base)
    (sheaf : (Scheme.QCoh.pullback base.left).obj y.sheaf ⟶ x.sheaf) :
    (homMk base sheaf).base = base :=
  sorry

/-- The sheaf component of `homMk` is the supplied pullback map. -/
theorem homMk_sheaf {S : Scheme.{u}} {x y : Obj S} (base : x.base ⟶ y.base)
    (sheaf : (Scheme.QCoh.pullback base.left).obj y.sheaf ⟶ x.sheaf) :
    (homMk base sheaf).sheaf = sheaf :=
  sorry

/-- The identity morphism uses the unit comparison of `QCoh.pseudofunctor`. -/
def Hom.id {S : Scheme.{u}} (x : Obj S) : Hom x x where
  fst := 𝟙 x.base
  snd := (Scheme.QCoh.pseudofunctor.mapId ⟨op x.base.left⟩).hom.toNatTrans.app x.sheaf

/-- The sheaf component of a composite morphism, using `mapComp` then whiskering. -/
def Hom.compSheaf {S : Scheme.{u}} {x y z : Obj S} (α : Hom x y) (β : Hom y z) :
    (Scheme.QCoh.pullback (α.base ≫ β.base).left).obj z.sheaf ⟶ x.sheaf :=
  (Scheme.QCoh.pseudofunctor.mapComp β.base.left.op.toLoc
      α.base.left.op.toLoc).hom.toNatTrans.app z.sheaf ≫
    (Scheme.QCoh.pullback α.base.left).map β.sheaf ≫ α.sheaf

/-- Composition of morphisms is composition of `S`-maps and of pullback maps of sheaves. -/
def Hom.compHom {S : Scheme.{u}} {x y z : Obj S} (α : Hom x y) (β : Hom y z) : Hom x z where
  fst := α.base ≫ β.base
  snd := Hom.compSheaf α β

/-- Left composition by an identity morphism leaves a `QCohStack` morphism unchanged. -/
theorem Hom.id_comp {S : Scheme.{u}} {x y : Obj S} (α : Hom x y) :
    Hom.compHom (Hom.id x) α = α := sorry

/-- Right composition by an identity morphism leaves a `QCohStack` morphism unchanged. -/
theorem Hom.comp_id {S : Scheme.{u}} {x y : Obj S} (α : Hom x y) :
    Hom.compHom α (Hom.id y) = α := sorry

/-- Composition of `QCohStack` morphisms is associative. -/
theorem Hom.assoc {S : Scheme.{u}} {w x y z : Obj S} (α : Hom w x) (β : Hom x y)
    (γ : Hom y z) :
    Hom.compHom (Hom.compHom α β) γ = Hom.compHom α (Hom.compHom β γ) := sorry

/-- Pairs `(X, F)` and morphisms `(f, f* F ⟶ G)` form a category. -/
instance category (S : Scheme.{u}) : Category (Obj S) where
  Hom := Hom
  id := Hom.id
  comp := fun α β ↦ Hom.compHom α β
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The projection `(X, F) ↦ X` from `QCohStack` to `(Sch/S)`. -/
def p (S : Scheme.{u}) : Obj S ⥤ Over S where
  obj x := x.base
  map α := α.base

/-- The object part of `p` is the underlying `S`-scheme. -/
theorem p_obj {S : Scheme.{u}} (x : Obj S) : (p S).obj x = x.base :=
  sorry

/-- The morphism part of `p` is the underlying `S`-morphism. -/
theorem p_map {S : Scheme.{u}} {x y : Obj S} (α : x ⟶ y) : (p S).map α = α.base :=
  sorry

/-- Morphisms `(Y, G) ⟶ (X, F)` are pairs consisting of `f : Y ⟶ X` over `S` and
`f* F ⟶ G` in `QCoh Y`. -/
def homSigma {S : Scheme.{u}} (x y : Obj S) :
    (x ⟶ y) ≃
      Σ (f : x.base ⟶ y.base), ((Scheme.QCoh.pullback f.left).obj y.sheaf ⟶ x.sheaf) where
  toFun := fun φ ↦ ⟨φ.base, φ.sheaf⟩
  invFun := fun pair ↦ homMk pair.1 pair.2
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Applying `homSigma` extracts the base morphism and the sheaf map. -/
@[simp]
theorem homSigma_apply {S : Scheme.{u}} {x y : Obj S} (φ : x ⟶ y) :
    homSigma x y φ = ⟨φ.base, φ.sheaf⟩ :=
  sorry

/-- The inverse of `homSigma` is `homMk`. -/
@[simp]
theorem homSigma_symm_apply {S : Scheme.{u}} {x y : Obj S}
    (pair : Σ (f : x.base ⟶ y.base), ((Scheme.QCoh.pullback f.left).obj y.sheaf ⟶ x.sheaf)) :
    (homSigma x y).symm pair = homMk pair.1 pair.2 :=
  sorry

end AlgebraicGeometry.QCohStack
