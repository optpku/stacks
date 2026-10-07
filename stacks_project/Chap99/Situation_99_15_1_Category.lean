module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap99.Lemma_99_13_1_Spaces

/-!
# The category of families of curves

The category of families of curves over schemes over a base is the full
subcategory of `FpFlatProperGroupoids` on objects whose structure morphism has
relative dimension at most `1`. Morphisms are the inherited cartesian squares,
and the forgetful functor to `Over S` presents the category over `Sch_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- Objects of `FpFlatProperGroupoids S` whose structure morphism has relative
dimension at most `d`. -/
def relativeDimensionLE (S : Scheme.{u}) (d : ℕ) :
    ObjectProperty (FpFlatProperGroupoids S) :=
  fun P ↦ RelativeDimensionLE P.obj.obj.obj.hom d

/-- Membership in `relativeDimensionLE S d` is the relative-dimension bound on
the structure morphism. -/
theorem relativeDimensionLE_iff {S : Scheme.{u}} {d : ℕ}
    (P : FpFlatProperGroupoids S) :
    relativeDimensionLE S d P ↔ RelativeDimensionLE P.obj.obj.obj.hom d :=
  sorry

/-- The category of families of curves over schemes over `S`: objects are
fp-flat-proper morphisms of algebraic spaces of relative dimension at most `1`,
and morphisms are cartesian squares. -/
abbrev Obj (S : Scheme.{u}) :=
  (relativeDimensionLE S 1).FullSubcategory

/-- Package an `FpFlatProper` morphism of relative dimension at most `1` as an
object of `Obj S`. -/
def mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    Obj S :=
  { obj := FpFlatProperGroupoids.mk pX,
    property := (inferInstance : RelativeDimensionLE pX 1) }

/-- The underlying `FpFlatProperGroupoids` object of `mk pX` is
`FpFlatProperGroupoids.mk pX`. -/
theorem mk_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    (mk pX).obj = FpFlatProperGroupoids.mk pX :=
  sorry

/-- The total space of a family of curves. -/
abbrev space {S : Scheme.{u}} (P : Obj S) : AlgebraicSpace S :=
  P.obj.obj.obj.obj.left

/-- The base scheme of a family of curves, as an object of `Over S`. -/
abbrev base {S : Scheme.{u}} (P : Obj S) : Over S :=
  P.obj.obj.obj.obj.right

/-- The structure morphism of a family of curves. -/
abbrev hom {S : Scheme.{u}} (P : Obj S) : space P ⟶ ofOver (base P) :=
  P.obj.obj.obj.obj.hom

/-- The total space of `mk pX` is `X`. -/
theorem mk_space {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    space (mk pX) = X :=
  sorry

/-- The base of `mk pX` is `U`. -/
theorem mk_base {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    base (mk pX) = U :=
  sorry

/-- The structure morphism of `mk pX` is `pX`. -/
theorem mk_hom {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    hom (mk pX) = pX :=
  sorry

/-- A family of curves is an fp-flat-proper morphism of relative dimension at
most `1`. -/
theorem spec {S : Scheme.{u}} (P : Obj S) :
    FpFlatProper (hom P) ∧ FinitePresentation (hom P) ∧ Flat (hom P) ∧
      Proper (hom P) ∧ RelativeDimensionLE (hom P) 1 :=
  sorry

/-- The full-subcategory inclusion `Obj S ⥤ FpFlatProperGroupoids S`. -/
abbrev inclusion (S : Scheme.{u}) : Obj S ⥤ FpFlatProperGroupoids S :=
  (relativeDimensionLE S 1).ι

/-- The inclusion of families of curves is full. -/
instance inclusion_full (S : Scheme.{u}) : (inclusion S).Full :=
  inferInstance

/-- The inclusion of families of curves is faithful. -/
instance inclusion_faithful (S : Scheme.{u}) : (inclusion S).Faithful :=
  inferInstance

/-- The inclusion sends `mk pX` to `FpFlatProperGroupoids.mk pX`. -/
theorem inclusion_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    (inclusion S).obj (mk pX) = FpFlatProperGroupoids.mk pX :=
  sorry

/-- The forgetful functor `Obj S ⥤ Over S`, sending a family of curves to its
base scheme over `S`. -/
abbrev p (S : Scheme.{u}) : Obj S ⥤ Over S :=
  (relativeDimensionLE S 1).ι ⋙ pFpFlatProperGroupoids S

/-- The projection `p` sends `mk pX` to the scheme `U` over `S`. -/
theorem p_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    (p S).obj (mk pX) = U :=
  sorry

/-- Curves as a category over `Sch_fppf`, via the forgetful functor `p`.
The Hom-universe is `u + 1` because `Category (AlgebraicSpace S)` is
`Category.{u + 1}`. -/
def over (S : Scheme.{u}) : BasedCategory.{u + 1, u + 1} (Over S) :=
  BasedCategory.ofFunctor (p S)

/-- The projection of `over S` is the forgetful functor `p S`. -/
theorem over_p (S : Scheme.{u}) : (over S).p = p S :=
  sorry

/-- The algebraic-space component of a morphism of families of curves. -/
abbrev spaceMap {S : Scheme.{u}} {P Q : Obj S} (φ : P ⟶ Q) :
    space P ⟶ space Q :=
  φ.hom.hom.hom.hom.left

/-- The base-scheme component of a morphism of families of curves. -/
abbrev baseMap {S : Scheme.{u}} {P Q : Obj S} (φ : P ⟶ Q) :
    base P ⟶ base Q :=
  φ.hom.hom.hom.hom.right

/-- A morphism of families of curves is a cartesian square of algebraic
spaces. -/
theorem hom_isPullback {S : Scheme.{u}} {P Q : Obj S} (φ : P ⟶ Q) :
    IsPullback (spaceMap φ) (hom P) (hom Q)
      ((ofOverFunctor S).map (baseMap φ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
