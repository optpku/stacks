/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Components
public import ReasLib.CategoryTheory.Sites.Sheafification.AddCommGrp

/-!
# Group structure on the relative Picard scheme

This file retains the Picard functor's group structure and identifies the degree-zero
component as an open and closed subgroup scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonObj Opposite
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.RelativePicard

/-- The Picard presheaf with its pointwise additive commutative group structure retained. -/
noncomputable def groupPresheaf {S : Scheme.{u}} (X : Over S) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of (T.unop ⊗ X).left.PicardGroup
  map g := AddCommGrpCat.ofHom (Scheme.Hom.picardPullback ((g.unop ▷ X).left))
  map_id := sorry
  map_comp := sorry

/-- Forgetting the group structure on `groupPresheaf X` recovers the Picard presheaf. -/
noncomputable def groupPresheafForgetIso {S : Scheme.{u}} (X : Over S) :
    groupPresheaf X ⋙ forget AddCommGrpCat ≅ presheaf X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The group-valued fppf sheafification of the Picard presheaf. -/
noncomputable def groupFunctor {S : Scheme.{u}} (X : Over S) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} :=
  (Scheme.fppfTopology.over S).sheafify (groupPresheaf X) ⋙
    AddCommGrpCat.toCommGrp ⋙ forget₂ CommGrpCat GrpCat

/-- Forgetting the multiplicative presentation of `groupFunctor X` gives the underlying
type-valued functor of its additive sheafification. -/
noncomputable def groupFunctorToAdditiveForgetIso {S : Scheme.{u}} (X : Over S) :
    groupFunctor X ⋙ forget GrpCat ≅
      (Scheme.fppfTopology.over S).sheafify (groupPresheaf X) ⋙ forget AddCommGrpCat :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The type-valued sheafification used in `functor X` has the same underlying values as the
corresponding sheafification functor. -/
noncomputable def functorSheafificationIso {S : Scheme.{u}} (X : Over S) :
    ((Scheme.fppfTopology.over S).sheafification (Type (u + 1))).obj (presheaf X) ≅
      (functor X).obj :=
  eqToIso (functor_val X).symm

/-- Forgetting the group structure on `groupFunctor X` recovers the relative Picard functor. -/
noncomputable def groupFunctorForgetIso {S : Scheme.{u}} (X : Over S) :
    groupFunctor X ⋙ forget GrpCat ≅ (functor X).obj :=
  groupFunctorToAdditiveForgetIso X ≪≫
    (Scheme.fppfTopology.over S).sheafifyCompIso
      (forget AddCommGrpCat.{u + 1}) (groupPresheaf X) ≪≫
    (eqToIso ((Scheme.fppfTopology.over S).sheafification_obj
      (Type (u + 1)) (groupPresheaf X ⋙ forget AddCommGrpCat))).symm ≪≫
    ((Scheme.fppfTopology.over S).sheafification (Type (u + 1))).mapIso
      (groupPresheafForgetIso X) ≪≫ functorSheafificationIso X

/-- The relative Picard scheme represents the underlying functor of `groupFunctor X`. -/
noncomputable def groupRepresentation {S : Scheme.{u}} (X : Over S)
    [(functor X).obj.IsRepresentable] :
    (groupFunctor X ⋙ forget GrpCat).RepresentableBy (scheme X) :=
  (schemeRepresentation X).ofIso (groupFunctorForgetIso X).symm

/-- The canonical group-object structure on the relative Picard scheme. -/
@[implicit_reducible]
noncomputable def schemeGrpObj {S : Scheme.{u}} (X : Over S)
    [(functor X).obj.IsRepresentable] : GrpObj (scheme X) :=
  GrpObj.ofRepresentableBy (scheme X) (groupFunctor X) (groupRepresentation X)

/-- At every test scheme, the degree-zero sections form a subgroup of the Picard group. -/
noncomputable def degreeZeroSectionSubgroup {S : Scheme.{u}} (X : Over S)
    (T : (Over S)ᵒᵖ) : Subgroup ((groupFunctor X).obj T) where
  carrier := {x | (groupFunctorForgetIso X).hom.app T x ∈ (degreeSubfunctor X 0).obj T}
  one_mem' := sorry
  mul_mem' := sorry
  inv_mem' := sorry

/-- The group-valued functor of degree-zero sections of the relative Picard functor. -/
noncomputable def degreeZeroGroupFunctor {S : Scheme.{u}} (X : Over S) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (degreeZeroSectionSubgroup X T)
  map f := GrpCat.ofHom
    { toFun := fun x ↦
        ⟨(groupFunctor X).map f x.1, sorry⟩
      map_one' := sorry
      map_mul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- Forgetting the group structure on `degreeZeroGroupFunctor X` recovers the degree-zero
Picard subfunctor. -/
noncomputable def degreeZeroGroupFunctorForgetIso {S : Scheme.{u}} (X : Over S) :
    degreeZeroGroupFunctor X ⋙ forget GrpCat ≅ (degreeSubfunctor X 0).toFunctor :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      { toFun := fun x ↦ ⟨(groupFunctorForgetIso X).hom.app T x.1, x.2⟩
        invFun := fun x ↦ ⟨(groupFunctorForgetIso X).inv.app T x.1, sorry⟩
        left_inv := sorry
        right_inv := sorry })
    (fun _ ↦ sorry)

/-- The degree-zero component represents the underlying functor of
`degreeZeroGroupFunctor X`. -/
noncomputable def degreeZeroGroupRepresentation {S : Scheme.{u}} (X : Over S)
    [(degreeSubfunctor X 0).toFunctor.IsRepresentable] :
    (degreeZeroGroupFunctor X ⋙ forget GrpCat).RepresentableBy (component X 0) :=
  (componentRepresentation X 0).ofIso (degreeZeroGroupFunctorForgetIso X).symm

/-- The canonical group-object structure on the degree-zero Picard component. -/
@[implicit_reducible]
noncomputable def componentZeroGrpObj {S : Scheme.{u}} (X : Over S)
    [(degreeSubfunctor X 0).toFunctor.IsRepresentable] : GrpObj (component X 0) :=
  GrpObj.ofRepresentableBy (component X 0) (degreeZeroGroupFunctor X)
    (degreeZeroGroupRepresentation X)

/-- The unit, multiplication, and inverse of the degree-zero component factor the
corresponding operations on the Picard scheme through its component inclusion. -/
noncomputable def componentZeroFactorization {S : Scheme.{u}} (X : Over S)
    [(degreeSubfunctor X 0).toFunctor.IsRepresentable]
    [(functor X).obj.IsRepresentable] :
    @GrpObj.Factorization (Over S) _ _ (component X 0) (scheme X)
      (schemeGrpObj X) (componentInclusion X 0) := by
  -- Local instance justification (proof-local temporary data): the explicit Picard group object is installed only while constructing its operation factorization.
  letI := schemeGrpObj X
  exact
    { one := (componentZeroGrpObj X).toMonObj.one
      mul := (componentZeroGrpObj X).toMonObj.mul
      inv := (componentZeroGrpObj X).inv
      one_hom := sorry
      mul_hom := sorry
      inv_hom := sorry }

/-- The component-zero factorization satisfies the unit, multiplication, and inverse
compatibility equations. -/
theorem componentZeroFactorization_spec {S : Scheme.{u}} (X : Over S)
    [(degreeSubfunctor X 0).toFunctor.IsRepresentable]
    [(functor X).obj.IsRepresentable] :
    @GrpObj.Factorization.one (Over S) _ _ (component X 0) (scheme X)
        (schemeGrpObj X) (componentInclusion X 0) (componentZeroFactorization X) ≫
        componentInclusion X 0 =
        (schemeGrpObj X).toMonObj.one ∧
      @GrpObj.Factorization.mul (Over S) _ _ (component X 0) (scheme X)
          (schemeGrpObj X) (componentInclusion X 0) (componentZeroFactorization X) ≫
          componentInclusion X 0 =
        (componentInclusion X 0 ⊗ₘ componentInclusion X 0) ≫
          (schemeGrpObj X).toMonObj.mul ∧
      @GrpObj.Factorization.inv (Over S) _ _ (component X 0) (scheme X)
          (schemeGrpObj X) (componentInclusion X 0) (componentZeroFactorization X) ≫
          componentInclusion X 0 =
        componentInclusion X 0 ≫ (schemeGrpObj X).inv := sorry

/-- The inclusion of the degree-zero component preserves the Picard group-object
operations. -/
theorem componentZeroInclusion_isMonHom {S : Scheme.{u}} (X : Over S)
    [(degreeSubfunctor X 0).toFunctor.IsRepresentable]
    [(functor X).obj.IsRepresentable] :
    @IsMonHom (Over S) _ _ (component X 0) (scheme X)
      (componentZeroGrpObj X).toMonObj (schemeGrpObj X).toMonObj
      (componentInclusion X 0) := sorry

/-- The degree-zero component is the closed subgroup scheme of the Picard scheme whose
inclusion is `componentInclusion X 0`. -/
noncomputable def degreeZeroClosedSubgroup
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] :
    @Scheme.ClosedSubgroup _ (scheme X) (schemeGrpObj X) := by
  -- Local instance justification (proof-local temporary data): the explicit Picard group object is installed only for the closed-subgroup constructor.
  letI := schemeGrpObj X
  -- Local instance justification (proof-local temporary data): the explicit degree-zero group object is installed only for the closed-subgroup constructor.
  letI := componentZeroGrpObj X
  -- Local instance justification (proof-local temporary data): the named preservation theorem is installed only for the closed-subgroup constructor.
  letI : IsMonHom (componentInclusion X 0) := componentZeroInclusion_isMonHom X
  exact Scheme.ClosedSubgroup.mk (componentInclusion X 0)

/-- The closed subgroup scheme's underlying inclusion is the degree-zero component
inclusion. -/
theorem degreeZeroClosedSubgroup_inclusion
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] :
    @Scheme.ClosedSubgroup.inclusion _ (scheme X) (schemeGrpObj X)
      (degreeZeroClosedSubgroup X) = componentInclusion X 0 := sorry

/-- The inclusion of the degree-zero closed subgroup scheme is also an open immersion. -/
instance degreeZeroClosedSubgroup_isOpenImmersion
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] :
    IsOpenImmersion
      (@Scheme.ClosedSubgroup.inclusion _ (scheme X) (schemeGrpObj X)
        (degreeZeroClosedSubgroup X)).left := sorry

/-- The additive subgroup of `k`-valued Picard classes carried by the degree-zero
subgroup scheme. -/
noncomputable def degreeZeroClasses
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] : AddSubgroup X.left.PicardGroup where
  carrier := degreeClasses X 0
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- The degree-zero Picard subgroup has exactly the degree-zero Picard classes as elements. -/
theorem mem_degreeZeroClasses
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (x : X.left.PicardGroup) :
    x ∈ degreeZeroClasses X ↔ x ∈ degreeClasses X 0 := sorry

/-- The `k`-points of the degree-zero subgroup scheme are classified by degree-zero
invertible-module classes. -/
theorem degreeZeroClosedSubgroup_kPoints
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] :
    Function.Bijective
      (degreeClassToComponentPoint X 0 :
        degreeClasses X 0 →
          ((𝟙_ (SchemeOverField k)) ⟶ (degreeZeroClosedSubgroup X).left.X)) := sorry

end AlgebraicGeometry.RelativePicard
