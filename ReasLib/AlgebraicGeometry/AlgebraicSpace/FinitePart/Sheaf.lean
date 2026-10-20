module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfSheaf
public import Mathlib.CategoryTheory.Sites.Sheaf

/-! # The fppf sheaf of actual finite-part pairs -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePart.Point

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The open subspace of the fibre product determined by a finite-part pair. -/
def subspace {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    OpenSubspace (pullback p.a f) :=
  OpenSubspace.fromOpens p.Z

/-- The points of the open subspace of a finite-part pair recover its open set. -/
theorem subspace_pointsOpens {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    p.subspace.pointsOpens = p.Z := by
  apply SetLike.coe_injective
  exact OpenSubspace.fromOpens_pointsSet p.Z

/-- A morphism and an open subspace finite over the test scheme determine a finite-part pair. -/
def ofSubspace {f : X ⟶ Y} {T : Over S} (a : ofOver T ⟶ Y)
    (W : OpenSubspace (pullback a f))
    [IsFinite (W.ι ≫ pullback.fst a f)] : Point f T :=
  (SubspacePoint.of a W inferInstance).toPoint

/-- The subspace of the pair constructed from an open subspace is reconstructed from its points. -/
theorem ofSubspace_subspace {f : X ⟶ Y} {T : Over S} (a : ofOver T ⟶ Y)
    (W : OpenSubspace (pullback a f))
    [IsFinite (W.ι ≫ pullback.fst a f)] :
    (ofSubspace a W).subspace = OpenSubspace.fromOpens W.pointsOpens := rfl

/-- The open subspace of a finite-part pair is its specified open and is finite over the test scheme. -/
theorem subspace_spec {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    p.subspace = OpenSubspace.fromOpens p.Z ∧
      IsFinite (p.subspace.ι ≫ pullback.fst p.a f) :=
  ⟨rfl, p.isFinite⟩

end FinitePart.Point

namespace FinitePart

/-- The presheaf of actual finite-part pairs, with inverse image as restriction. -/
def pointsPresheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Point f T.unop
  map {T T'} h := TypeCat.ofHom fun (p : Point f T.unop) ↦ p.restrict h.unop
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro p
    exact Point.restrict_id p
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (Point.restrict_comp p h.unop k.unop).symm

/-- Actual finite-part pairs satisfy fppf descent. -/
theorem pointsPresheaf_isSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (pointsPresheaf f) := sorry

end FinitePart

/-- The fppf sheaf of finite-part pairs with values in the universe of actual pairs. -/
def finitePartSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨FinitePart.pointsPresheaf f, FinitePart.pointsPresheaf_isSheaf f⟩

/-- Sections of the finite-part sheaf are actual finite-part pairs. -/
theorem finitePartSheaf_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Over S) :
    (finitePartSheaf f).obj.obj (op T) = FinitePart.Point f T := rfl

/-- The underlying presheaf of the finite-part sheaf satisfies fppf descent. -/
theorem finitePartSheaf_isSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (finitePartSheaf f).obj :=
  (finitePartSheaf f).property

/-- Actual finite-part pairs are equivalent to the sections of the universe-shrunk finite-part presheaf. -/
def finitePartSheaf_equiv_finitePart {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : Over S) :
    FinitePart.Point f T ≃ (finitePart f).obj (op T) :=
  (finitePart_obj_equiv f T).symm

/-- The inverse comparison from actual pairs is the object equivalence of the finite-part presheaf. -/
theorem finitePartSheaf_equiv_finitePart_symm {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : Over S) :
    (finitePartSheaf_equiv_finitePart f T).symm = finitePart_obj_equiv f T := rfl

/-- The component of the structure morphism `(X/Y)_fin ⟶ Y` on a scheme `T` over `S`,
sending a pair `(a, Z)` to the universe-raised `Y`-section `Point.a_elem`. -/
def finitePartToApp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ) (p : FinitePart.Point f T.unop) :
    ((toFppfSheaf S).obj Y).obj.obj T :=
  ULift.up p.a_elem

/-- The projection from finite-part pairs to base sections commutes with restriction. -/
theorem finitePartTo_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (finitePartSheaf f).obj.map g ≫ TypeCat.ofHom (finitePartToApp f T') =
      TypeCat.ofHom (finitePartToApp f T) ≫ ((toFppfSheaf S).obj Y).obj.map g :=
  sorry

/-- The structure morphism `(X/Y)_fin ⟶ Y` of finite-part sheaves, sending a pair
`(a, Z)` to the morphism `a : T ⟶ Y`. -/
def finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    finitePartSheaf f ⟶ (toFppfSheaf S).obj Y :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom (finitePartToApp f T)
      naturality := fun _ _ g ↦ finitePartTo_naturality f g }

/-- Components of `finitePartTo` are `finitePartToApp`. -/
theorem finitePartTo_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ) :
    (finitePartTo f).hom.app T = TypeCat.ofHom (finitePartToApp f T) :=
  sorry

/-- On a pair `(a, Z)`, the structure morphism records `a` as the universe-raised
section `Point.a_elem`. -/
theorem finitePartTo_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T : Over S} (p : FinitePart.Point f T) :
    (finitePartTo f).hom.app (op T) p = ULift.up p.a_elem :=
  sorry

/-- The small-valued finite-part presheaf satisfies the fppf sheaf condition. -/
theorem finitePart_isSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (finitePart f) :=
  sorry

namespace FinitePart

/-- The small-valued fppf sheaf of finite-open pairs for a morphism of algebraic spaces. -/
def sheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨finitePart f, finitePart_isSheaf f⟩

/-- The underlying presheaf of the small-valued finite-part sheaf is the finite-part presheaf. -/
theorem sheaf_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheaf f).obj = finitePart f :=
  rfl

end FinitePart

end AlgebraicGeometry.AlgebraicSpace
