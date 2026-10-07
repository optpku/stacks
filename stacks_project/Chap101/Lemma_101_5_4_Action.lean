module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import stacks_project.Chap101.Lemma_101_5_4_Comparison

/-!
# Postcomposition action of relative automorphisms on relative isomorphisms

The sheaf `Isom^α_{X/Y}(x1, x2)` is an algebraic space over `Z`, and
`Isom_{X/Y}(x2, x2)` acts on it by postcomposition in the homotopy category of
algebraic spaces over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open AlgebraicGeometry.SpacesOver
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

/-- The relative isomorphism sheaf is an algebraic stack. -/
instance instAlgebraicStack_relativeIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    AlgebraicStack (relativeIsom f α) :=
  sorry

/-- The structure morphism `Isom^α_{X/Y}(x1, x2) ⟶ Z` is locally of finite type. -/
instance instLocallyOfFiniteType_relativeIsom_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    Groupoids.Hom.LocallyOfFiniteType (relativeIsom.snd f α) :=
  sorry

/-- The relative isomorphism sheaf, as an object of `SpacesOver` of
`Z.toGroupoids`. -/
def asSpacesOverIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    SpacesOver Z.toGroupoids :=
  SpacesOver.mk (relativeIsom.snd f α)
    (Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable _)

/-- The domain of `asSpacesOverIsom f α` is `relativeIsom f α`. -/
theorem asSpacesOverIsom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    SpacesOver.left (asSpacesOverIsom f α) = relativeIsom f α :=
  sorry

/-- The structural morphism of `asSpacesOverIsom f α` is `relativeIsom.snd f α`. -/
theorem asSpacesOverIsom_hom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    SpacesOver.hom (asSpacesOverIsom f α) = relativeIsom.snd f α :=
  sorry

/-- Packaged relative isomorphisms have algebraic-stack domain, and the
structure map to `Z` is representable by algebraic spaces. -/
theorem asSpacesOverIsom_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    AlgebraicStack (SpacesOver.left (asSpacesOverIsom f α)) ∧
      relativelyRepresentableByAlgebraicSpaces
        (SpacesOver.hom (asSpacesOverIsom f α)) :=
  sorry

/-- Relative isomorphisms as an object of the homotopy 1-category of
algebraic-space representable morphisms to `Z`. -/
def asHomotopyIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Bicategory.HomotopyCategory (SpacesOver Z.toGroupoids) :=
  Bicategory.HomotopyCategory.mk (asSpacesOverIsom f α)

/-- The underlying `SpacesOver` object of `asHomotopyIsom f α` is
`asSpacesOverIsom f α`. -/
theorem asHomotopyIsom_as {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    (asHomotopyIsom f α).as = asSpacesOverIsom f α :=
  sorry

/-- The sheaf of isomorphisms `Isom_X(x1, x2)`, as a groupoid fibration. -/
abbrev isomApex {S : Scheme.{u}} {X : GroupoidsOver S} {Z : AlgebraicSpace S}
    (x1 x2 : Z.toGroupoids ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2

/-- `isomApex x1 x2` is the 2-fibre product of `x1` against `x2`. -/
theorem isomApex_eq {S : Scheme.{u}} {X : GroupoidsOver S} {Z : AlgebraicSpace S}
    (x1 x2 : Z.toGroupoids ⟶ X) :
    isomApex x1 x2 = TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 :=
  sorry

/-- The chosen 2-fibre product of relative automorphisms of `x2` with
`Isom^α_{X/Y}(x1, x2)` over `Z`. -/
abbrev smulApex {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (fst f x2) (relativeIsom.snd f α)

/-- `smulApex f α` is the 2-fibre product of `fst f x2` against
`relativeIsom.snd f α`. -/
theorem smulApex_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulApex f α =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (fst f x2)
        (relativeIsom.snd f α) :=
  sorry

/-- The structure morphism of the product
`Isom_{X/Y}(x2, x2) ×_Z Isom^α_{X/Y}(x1, x2)` over `Z`. -/
def smulStructure {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulApex f α ⟶ Z.toGroupoids :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2) (relativeIsom.snd f α) ≫
    fst f x2

/-- `smulStructure f α` is the composite of the first product projection with
`fst f x2`. -/
theorem smulStructure_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2)
          (relativeIsom.snd f α) ≫
        fst f x2 :=
  sorry

/-- The tautological fibre automorphism of the universal object of relative
inertia. -/
def tautologicalAut {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    forget.{u + 1, u, u, u + 1} f ≅ forget.{u + 1, u, u, u + 1} f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (fun ξ ↦ ξ.aut) (fun _ ↦ sorry) (fun _ ↦ sorry))

/-- Identifying `x2` with the underlying object of relative inertia, along the
automorphism factor of the product over `Z`. -/
def smulAutIdent {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α ≫ x2 ≅
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2)
            (relativeIsom.snd f α) ≫
          snd f x2) ≫
        forget.{u + 1, u, u, u + 1} f :=
  α_ _ _ _ ≪≫
    whiskerLeftIso
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2)
          (relativeIsom.snd f α))
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} x2
          (forget.{u + 1, u, u, u + 1} f)) ≪≫
      (α_ _ _ _).symm

/-- The relative automorphism factor as a 2-endomorphism of `x2` over `Z`. -/
def smulAutIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α ≫ x2 ≅ smulStructure f α ≫ x2 :=
  smulAutIdent f α ≪≫
    whiskerLeftIso
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2)
            (relativeIsom.snd f α) ≫
          snd f x2)
        (tautologicalAut f) ≪≫
      (smulAutIdent f α).symm

/-- The first `Z`-leg of `Isom_X(x1, x2)` recovers the structure map of
`Isom^α_{X/Y}(x1, x2)`. -/
def relativeIsom.fst_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.fst f α ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} x1 x2 ≅
      relativeIsom.snd f α :=
  whiskerLeftIso (relativeIsom.fst f α) (ρ_ _).symm ≪≫
    whiskerLeftIso (relativeIsom.fst f α)
        (TwoFibreProduct.map.fstIso (pairComparisonCospan f x1 x2)).symm ≪≫
      (α_ _ _ _).symm ≪≫
        whiskerRightIso
            (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
              (pairComparison f x1 x2) (diagonalAlpha α))
            (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (x1 ≫ f)
              (x2 ≫ f)) ≪≫
          α_ _ _ _ ≪≫
            whiskerLeftIso (relativeIsom.snd f α) (diagonalAlpha_fst α) ≪≫
              ρ_ _

/-- The second `Z`-leg of `Isom_X(x1, x2)` recovers the structure map of
`Isom^α_{X/Y}(x1, x2)`. -/
def relativeIsom.fst_snd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.fst f α ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} x1 x2 ≅
      relativeIsom.snd f α :=
  whiskerLeftIso (relativeIsom.fst f α) (ρ_ _).symm ≪≫
    whiskerLeftIso (relativeIsom.fst f α)
        (TwoFibreProduct.map.sndIso (pairComparisonCospan f x1 x2)).symm ≪≫
      (α_ _ _ _).symm ≪≫
        whiskerRightIso
            (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
              (pairComparison f x1 x2) (diagonalAlpha α))
            (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (x1 ≫ f)
              (x2 ≫ f)) ≪≫
          α_ _ _ _ ≪≫
            whiskerLeftIso (relativeIsom.snd f α) (diagonalAlpha_snd α) ≪≫
              ρ_ _

/-- The isomorphism `x1 ≅ x2` carried by `Isom^α_{X/Y}(x1, x2)` over `Z`. -/
def relativeIsom.compIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.snd f α ≫ x1 ≅ relativeIsom.snd f α ≫ x2 :=
  whiskerRightIso (relativeIsom.fst_fst f α).symm x1 ≪≫
    α_ _ _ _ ≪≫
      whiskerLeftIso (relativeIsom.fst f α)
          (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} x1 x2) ≪≫
        (α_ _ _ _).symm ≪≫
          whiskerRightIso (relativeIsom.fst_snd f α) x2

/-- The isomorphism factor of the product, as a 2-cell `x1 ≅ x2` over `Z`. -/
def smulIsomIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α ≫ x1 ≅ smulStructure f α ≫ x2 :=
  whiskerRightIso
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (fst f x2)
        (relativeIsom.snd f α))
      x1 ≪≫
    α_ _ _ _ ≪≫
      whiskerLeftIso
          (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (fst f x2)
            (relativeIsom.snd f α))
          (relativeIsom.compIso f α) ≪≫
        (α_ _ _ _).symm ≪≫
          whiskerRightIso
              (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (fst f x2)
                (relativeIsom.snd f α)).symm
              x2

/-- Postcomposition of fibre isomorphisms `(φ, β) ↦ φ ≫ β` as a 2-cell over `Z`. -/
def smulCompIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α ≫ x1 ≅ smulStructure f α ≫ x2 :=
  smulIsomIso f α ≪≫ smulAutIso f α

/-- The cone over `x1, x2` presenting postcomposition of isomorphisms. -/
def smulToPairCone {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Bicategory.PseudoPullbackCone x1 x2 where
  pt := smulApex f α
  fst := smulStructure f α
  snd := smulStructure f α
  iso := smulCompIso f α

/-- Postcomposition of the automorphism factor with the isomorphism factor,
as a map into `Isom_X(x1, x2)`. -/
def smulToPair {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulApex f α ⟶ isomApex x1 x2 :=
  Bicategory.PseudoPullbackCone.lift (smulToPairCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x1 x2)

/-- Postcomposition followed by the first `Z`-leg of `Isom_X(x1, x2)` recovers
the structure morphism over `Z`. -/
def smulToPair_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulToPair f α ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} x1 x2 ≅
      smulStructure f α :=
  Bicategory.PseudoPullbackCone.lift.fstIso (smulToPairCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x1 x2)

/-- Postcomposition followed by the second `Z`-leg of `Isom_X(x1, x2)` recovers
the structure morphism over `Z`. -/
def smulToPair_snd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulToPair f α ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} x1 x2 ≅
      smulStructure f α :=
  Bicategory.PseudoPullbackCone.lift.sndIso (smulToPairCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x1 x2)

/-- After applying `f`, postcomposition and the original isomorphism have the
same first projection to `Z`. -/
def smulIsoLegsFst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulToPair f α ≫ pairComparison f x1 x2 ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) ≅
      smulStructure f α ≫ diagonalAlpha α ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) :=
  whiskerLeftIso (smulToPair f α)
      (TwoFibreProduct.map.fstIso (pairComparisonCospan f x1 x2)) ≪≫
    whiskerLeftIso (smulToPair f α) (ρ_ _) ≪≫
      smulToPair_fst f α ≪≫
        (ρ_ (smulStructure f α)).symm ≪≫
          whiskerLeftIso (smulStructure f α) (diagonalAlpha_fst α).symm

/-- After applying `f`, postcomposition and the original isomorphism have the
same second projection to `Z`. -/
def smulIsoLegsSnd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulToPair f α ≫ pairComparison f x1 x2 ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) ≅
      smulStructure f α ≫ diagonalAlpha α ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) :=
  whiskerLeftIso (smulToPair f α)
      (TwoFibreProduct.map.sndIso (pairComparisonCospan f x1 x2)) ≪≫
    whiskerLeftIso (smulToPair f α) (ρ_ _) ≪≫
      smulToPair_snd f α ≪≫
        (ρ_ (smulStructure f α)).symm ≪≫
          whiskerLeftIso (smulStructure f α) (diagonalAlpha_snd α).symm

/-- Objectwise first-leg comparison of postcomposition against the diagonal of
`α` in `Isom_Y(f ∘ x1, f ∘ x2)`. -/
def smulIsoFstObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    BasedCategory.PseudoPullback.fstObj
        ((toFunctor (smulToPair f α ≫ pairComparison f x1 x2)).obj p) ≅
      BasedCategory.PseudoPullback.fstObj
        ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p) :=
  Iso.mk ((toNatTrans (smulIsoLegsFst f α).hom).app p)
    ((toNatTrans (smulIsoLegsFst f α).inv).app p) sorry sorry

/-- Objectwise second-leg comparison of postcomposition against the diagonal of
`α` in `Isom_Y(f ∘ x1, f ∘ x2)`. -/
def smulIsoSndObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    BasedCategory.PseudoPullback.sndObj
        ((toFunctor (smulToPair f α ≫ pairComparison f x1 x2)).obj p) ≅
      BasedCategory.PseudoPullback.sndObj
        ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p) :=
  Iso.mk ((toNatTrans (smulIsoLegsSnd f α).hom).app p)
    ((toNatTrans (smulIsoLegsSnd f α).inv).app p) sorry sorry

/-- Objectwise comparison of postcomposition against the diagonal of `α` in
`Isom_Y(f ∘ x1, f ∘ x2)`. -/
def smulIsoApp {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    (toFunctor (smulToPair f α ≫ pairComparison f x1 x2)).obj p ≅
      (toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p :=
  BasedCategory.PseudoPullback.mkIso
    ((BasedCategory.PseudoPullback.fstBaseIso
          ((toFunctor (smulToPair f α ≫ pairComparison f x1 x2)).obj p)).symm ≪≫
      (Z.toGroupoids.p.mapIso (smulIsoFstObj f α p)) ≪≫
        BasedCategory.PseudoPullback.fstBaseIso
          ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p))
    (smulIsoFstObj f α p) (smulIsoSndObj f α p) sorry sorry sorry

/-- The 2-isomorphism witnessing that postcomposition equalizes `pairComparison`
against `diagonalAlpha`, using that the automorphism factor maps to the identity
in `Y`. -/
def smulIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulToPair f α ≫ pairComparison f x1 x2 ≅
      smulStructure f α ≫ diagonalAlpha α :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (smulIsoApp f α) (fun _ ↦ sorry) (fun _ ↦ sorry))

/-- The postcomposition cone of relative isomorphisms over `Z`. -/
def smulCone {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Bicategory.PseudoPullbackCone (pairComparison f x1 x2) (diagonalAlpha α) where
  pt := smulApex f α
  fst := smulToPair f α
  snd := smulStructure f α
  iso := smulIso f α

/-- Postcomposition
`(Z ×_X I_{X/Y}) ×_Z Isom^α_{X/Y}(x1, x2) ⟶ Isom^α_{X/Y}(x1, x2)`. -/
def smulMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulApex f α ⟶ relativeIsom f α :=
  Bicategory.PseudoPullbackCone.lift (smulCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (pairComparison f x1 x2) (diagonalAlpha α))

/-- Postcomposition followed by the comparison into `Isom_X(x1, x2)` recovers
the composition of fibre isomorphisms. -/
def smulMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulMap f α ≫ relativeIsom.fst f α ≅ smulToPair f α :=
  Bicategory.PseudoPullbackCone.lift.fstIso (smulCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (pairComparison f x1 x2) (diagonalAlpha α))

/-- Postcomposition followed by the structure map to `Z` recovers the structure
morphism of the binary product over `Z`. -/
def smulMap_snd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulMap f α ≫ relativeIsom.snd f α ≅ smulStructure f α :=
  Bicategory.PseudoPullbackCone.lift.sndIso (smulCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (pairComparison f x1 x2) (diagonalAlpha α))

/-- The action 1-morphism of relative automorphisms on relative isomorphisms in
`SpacesOver Z.toGroupoids`. -/
def smulHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    tensor (asSpacesOver f x2) (asSpacesOverIsom f α) ⟶ asSpacesOverIsom f α :=
  SpacesOver.homMk (smulMap f α) (smulMap_snd f α).symm

/-- The underlying domain map of `smulHom f α` is `smulMap f α`. -/
theorem smulHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    SpacesOver.map (smulHom f α) = smulMap f α :=
  sorry

/-- The canonical module-object structure of `Isom_{X/Y}(x2, x2)` on
`Isom^α_{X/Y}(x1, x2)`. -/
instance instModObj_relativeIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    ModObj (asHomotopy f x2) (asHomotopyIsom f α) where
  smul := Bicategory.HomotopyCategory.mkHom (smulHom f α)
  one_smul := sorry
  mul_smul := sorry

/-- The action of `Isom_{X/Y}(x2, x2)` on `Isom^α_{X/Y}(x1, x2)` over `Z`. -/
def action {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Mod (Bicategory.HomotopyCategory (SpacesOver Z.toGroupoids))
      (asHomotopy f x2) where
  X := asHomotopyIsom f α

/-- The underlying object of `action f α` is `asHomotopyIsom f α`. -/
theorem action_X {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    (action f α).X = asHomotopyIsom f α :=
  sorry

/-- `Isom^α_{X/Y}(x1, x2)` is a pseudo-torsor for `Isom_{X/Y}(x2, x2)` over `Z`. -/
instance instIsPseudoTorsor_action {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Mod.IsPseudoTorsor (action f α) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
