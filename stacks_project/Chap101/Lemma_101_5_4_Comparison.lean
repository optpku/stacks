module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Naturality
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import stacks_project.Chap101.Definition_101_5_3_Group
public import stacks_project.Chap101.Definition_101_5_3_Isom

/-!
# Kernel and comparison maps of relative automorphism sheaves

For a morphism `f : X ⟶ Y` of algebraic stacks and a morphism `x : Z ⟶ X`
from an algebraic space, the relative automorphism sheaf sits in a left-exact
sequence of group objects
`Isom_{X/Y}(x, x) ⟶ Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` in the homotopy
category of algebraic spaces over `Z`. The relative isomorphism sheaf is the
apex of the 2-fibre product of `pairComparison` against `diagonalAlpha`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

/-- The invertible square sending relative inertia of `f` to relative inertia
of the base projection of `X`. -/
def kernelSquareIso {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    f ≫ baseProjection.{u + 1, u, u + 1} Y ≅
      𝟙 X ≫ baseProjection.{u + 1, u, u + 1} X :=
  eqToIso (comp_baseProjection f) ≪≫
    (λ_ (baseProjection.{u + 1, u, u + 1} X)).symm

/-- The cospan transformation presenting the kernel inclusion
`Z ×_X I_{X/Y} ⟶ Z ×_X I_X`. -/
def kernelCospan {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    CospanTransform x (forget.{u + 1, u, u, u + 1} f) x
      (forget.{u + 1, u, u, u + 1}
        (baseProjection.{u + 1, u, u + 1} X)) :=
  CospanTransform.mk (𝟙 Z.toGroupoids)
    (RelativeInertia.map.{u + 1, u, u, u + 1} (𝟙 X)
      (baseProjection.{u + 1, u, u + 1} Y) (kernelSquareIso f))
    (𝟙 X) (λ_ x ≪≫ (ρ_ x).symm)
    (eqToIso
      (RelativeInertia.map.comp_forget.{u + 1, u, u, u + 1} (𝟙 X)
        (baseProjection.{u + 1, u, u + 1} Y) (kernelSquareIso f)))

/-- The left vertex of `kernelCospan f x` is the identity of `Z`. -/
theorem kernelCospan_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    (kernelCospan f x).left = 𝟙 Z.toGroupoids :=
  sorry

/-- The base vertex of `kernelCospan f x` is the identity of `X`. -/
theorem kernelCospan_base {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    (kernelCospan f x).base = 𝟙 X :=
  sorry

/-- The kernel inclusion `Isom_{X/Y}(x, x) ⟶ Isom_X(x, x)` as a 1-morphism of
groupoid fibrations. -/
def kernelιMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    relativeAut f x ⟶ relativeAut (baseProjection.{u + 1, u, u + 1} X) x :=
  TwoFibreProduct.map (kernelCospan f x)

/-- `kernelιMap f x` is the two-fibre-product map of `kernelCospan f x`. -/
theorem kernelιMap_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    kernelιMap f x = TwoFibreProduct.map (kernelCospan f x) :=
  sorry

/-- The kernel inclusion followed by the structure map of `Isom_X(x, x)` recovers
the structure map of `Isom_{X/Y}(x, x)`. -/
def kernelιMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    kernelιMap f x ≫ fst (baseProjection.{u + 1, u, u + 1} X) x ≅ fst f x :=
  TwoFibreProduct.map.fstIso (kernelCospan f x) ≪≫ ρ_ (fst f x)

/-- The kernel inclusion as a 1-morphism of `SpacesOver Z.toGroupoids`. -/
def kernelιHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asSpacesOver f x ⟶
      asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x :=
  SpacesOver.homMk (kernelιMap f x) (kernelιMap_fst f x).symm

/-- The underlying domain map of `kernelιHom f x` is `kernelιMap f x`. -/
theorem kernelιHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    SpacesOver.map (kernelιHom f x) = kernelιMap f x :=
  sorry

/-- The kernel inclusion of relative automorphisms in the homotopy category of
algebraic spaces over `Z`. -/
def kernelι {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asHomotopy f x ⟶ asHomotopy (baseProjection.{u + 1, u, u + 1} X) x :=
  Bicategory.HomotopyCategory.mkHom (kernelιHom f x)

/-- `kernelι f x` is the homotopy class of `kernelιHom f x`. -/
theorem kernelι_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    kernelι f x = Bicategory.HomotopyCategory.mkHom (kernelιHom f x) :=
  sorry

/-- The invertible square sending relative inertia of the base projection of `X`
to relative inertia of the base projection of `Y`. -/
def toTargetSquareIso {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    baseProjection.{u + 1, u, u + 1} X ≫
        𝟙 (base.{u + 1, u, u + 1} (Over S)) ≅
      f ≫ baseProjection.{u + 1, u, u + 1} Y :=
  ρ_ (baseProjection.{u + 1, u, u + 1} X) ≪≫
    eqToIso (comp_baseProjection f).symm

/-- The cospan transformation presenting
`Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)`. -/
def toTargetCospan {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    CospanTransform x
      (forget.{u + 1, u, u, u + 1} (baseProjection.{u + 1, u, u + 1} X))
      (x ≫ f)
      (forget.{u + 1, u, u, u + 1} (baseProjection.{u + 1, u, u + 1} Y)) :=
  CospanTransform.mk (𝟙 Z.toGroupoids)
    (RelativeInertia.map.{u + 1, u, u, u + 1} f
      (𝟙 (base.{u + 1, u, u + 1} (Over S))) (toTargetSquareIso f))
    f (λ_ (x ≫ f))
    (eqToIso
      (RelativeInertia.map.comp_forget.{u + 1, u, u, u + 1} f
        (𝟙 (base.{u + 1, u, u + 1} (Over S))) (toTargetSquareIso f)))

/-- The left vertex of `toTargetCospan f x` is the identity of `Z`. -/
theorem toTargetCospan_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    (toTargetCospan f x).left = 𝟙 Z.toGroupoids :=
  sorry

/-- The base vertex of `toTargetCospan f x` is `f`. -/
theorem toTargetCospan_base {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    (toTargetCospan f x).base = f :=
  sorry

/-- The comparison `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` as a 1-morphism of
groupoid fibrations. -/
def toTargetMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    relativeAut (baseProjection.{u + 1, u, u + 1} X) x ⟶
      relativeAut (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  TwoFibreProduct.map (toTargetCospan f x)

/-- `toTargetMap f x` is the two-fibre-product map of `toTargetCospan f x`. -/
theorem toTargetMap_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    toTargetMap f x = TwoFibreProduct.map (toTargetCospan f x) :=
  sorry

/-- `toTargetMap` commutes with structure maps to `Z` up to the identity unitor. -/
def toTargetMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    toTargetMap f x ≫ fst (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) ≅
      fst (baseProjection.{u + 1, u, u + 1} X) x :=
  TwoFibreProduct.map.fstIso (toTargetCospan f x) ≪≫
    ρ_ (fst (baseProjection.{u + 1, u, u + 1} X) x)

/-- The comparison `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` as a 1-morphism of
`SpacesOver Z.toGroupoids`. -/
def toTargetHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x ⟶
      asSpacesOver (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  SpacesOver.homMk (toTargetMap f x) (toTargetMap_fst f x).symm

/-- The underlying domain map of `toTargetHom f x` is `toTargetMap f x`. -/
theorem toTargetHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    SpacesOver.map (toTargetHom f x) = toTargetMap f x :=
  sorry

/-- The comparison `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` in the homotopy
category of algebraic spaces over `Z`. -/
def toTarget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asHomotopy (baseProjection.{u + 1, u, u + 1} X) x ⟶
      asHomotopy (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  Bicategory.HomotopyCategory.mkHom (toTargetHom f x)

/-- `toTarget f x` is the homotopy class of `toTargetHom f x`. -/
theorem toTarget_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    toTarget f x = Bicategory.HomotopyCategory.mkHom (toTargetHom f x) :=
  sorry

/-- The trivial homomorphism `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` through the
unit section of the target. -/
def constOneHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x ⟶
      asSpacesOver (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  SpacesOver.toId (asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x) ≫
    oneHom (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f)

/-- The underlying domain map of `constOneHom f x` is the composite of the
structure map of `Isom_X(x, x)` with the unit of `Isom_Y(f ∘ x, f ∘ x)`. -/
theorem constOneHom_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    constOneHom f x =
      SpacesOver.toId (asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x) ≫
        oneHom (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  sorry

/-- The trivial homomorphism `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` in the
homotopy category of algebraic spaces over `Z`. -/
def constOne {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asHomotopy (baseProjection.{u + 1, u, u + 1} X) x ⟶
      asHomotopy (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  Bicategory.HomotopyCategory.mkHom (constOneHom f x)

/-- `constOne f x` is the homotopy class of `constOneHom f x`. -/
theorem constOne_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    constOne f x = Bicategory.HomotopyCategory.mkHom (constOneHom f x) :=
  sorry

/-- The kernel inclusion equalizes `toTarget` and the trivial homomorphism. -/
theorem kernelι_comp_toTarget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    kernelι f x ≫ toTarget f x = kernelι f x ≫ constOne f x :=
  sorry

/-- The kernel inclusion is a homomorphism of group objects. -/
instance instIsMonHom_kernelι {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    IsMonHom (kernelι f x) :=
  sorry

/-- The comparison `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` is a homomorphism of
group objects. -/
instance instIsMonHom_toTarget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    IsMonHom (toTarget f x) :=
  sorry

/-- The relative automorphism sheaf is the kernel of
`Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` at the identity section. -/
theorem isomExactSequence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X)
    {G : Bicategory.HomotopyCategory (SpacesOver Z.toGroupoids)}
    (φ : G ⟶ asHomotopy (baseProjection.{u + 1, u, u + 1} X) x) :
    (∃! ψ : G ⟶ asHomotopy f x, ψ ≫ kernelι f x = φ) ↔
      φ ≫ toTarget f x = φ ≫ constOne f x :=
  sorry

/-- The left vertical of the source cartesian square, landing in
`Isom_X(x1, x2)`. -/
def relativeIsom.fst {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom f α ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u}
    (pairComparison f x1 x2) (diagonalAlpha α)

/-- `relativeIsom.fst f α` is the first 2-fibre-product projection. -/
theorem relativeIsom.fst_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.fst f α =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u}
        (pairComparison f x1 x2) (diagonalAlpha α) :=
  sorry

/-- The structure morphism `Isom^α_{X/Y}(x1, x2) ⟶ Z`. -/
def relativeIsom.snd {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom f α ⟶ Z.toGroupoids :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u}
    (pairComparison f x1 x2) (diagonalAlpha α)

/-- `relativeIsom.snd f α` is the second 2-fibre-product projection. -/
theorem relativeIsom.snd_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.snd f α =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u}
        (pairComparison f x1 x2) (diagonalAlpha α) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
