module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.Algebra.Module.LinearMap.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Operations
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.CospanPullback

/-!
# Tangent algebra of deformation functors

The dual-number cogroup operations induce vector-space operations on the values of
a deformation functor. Natural transformations induce linear maps on these values.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat

universe u v

namespace CategoryTheory.Functor

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
  [IsDeformationCategory (CategoryOfElements.π F)]

/-- The unique value of a deformation functor at the residue field. -/
def tangentResiduePoint : F.obj (residue Λ k) :=
  let fiberObject := IsPredeformationCategory.nonempty_residueFiber
    (p := CategoryOfElements.π F) |>.some
  F.map (eqToHom fiberObject.property) fiberObject.val.2

/-- The canonical zero tangent vector is the image of the unique residue value. -/
def tangentZero : F.obj (dualNumber Λ k) :=
  F.map (residueToDualNumber Λ k) (tangentResiduePoint F)

/-- Every residue value gives the canonical zero, and all reductions have the unique
residue value. -/
theorem tangentZero_spec :
    (∀ residuePoint : F.obj (residue Λ k), residuePoint = tangentResiduePoint F) ∧
      (∀ residuePoint : F.obj (residue Λ k),
        F.map (residueToDualNumber Λ k) residuePoint = tangentZero F) := sorry

/-- Two compatible maps to the dual numbers induce the explicit algebra-pullback map. -/
def tangentSelfPullbackLift {base : ArtinianLocalAlgCat Λ k}
    (left right : base ⟶ dualNumber Λ k)
    (compatibility : left ≫ dualNumberToResidue Λ k = right ≫ dualNumberToResidue Λ k) :
    base ⟶ dualNumberSelfPullback Λ := by
  have identityCompatibility :
      𝟙 (dualNumber Λ k) ≫ dualNumberToResidue Λ k = dualNumberToResidue Λ k := by simp
  have objectEquality :
      cospanPullback (dualNumberToResidue Λ k) (dualNumberToResidue Λ k)
        (𝟙 (dualNumber Λ k)) identityCompatibility = dualNumberSelfPullback Λ := by
    unfold cospanPullback dualNumberSelfPullback
    congr 1
  exact cospanPullbackLift (B := base) (A := residue Λ k)
    (A1 := dualNumber Λ k) (A2 := dualNumber Λ k)
    (dualNumberToResidue Λ k) (dualNumberToResidue Λ k)
    (𝟙 (dualNumber Λ k)) identityCompatibility left right compatibility ≫ eqToHom objectEquality

/-- The canonical lift of a pair of tangent vectors to the self-pullback of the dual
numbers, obtained from the supplied Rim-Schlessinger pullback. -/
def tangentPairLift (left right : F.obj (dualNumber Λ k)) :
    F.obj (dualNumberSelfPullback Λ) := by
  let leftObject : F.Elements := ⟨dualNumber Λ k, left⟩
  let rightObject : F.Elements := ⟨dualNumber Λ k, right⟩
  let residueObject : F.Elements := ⟨residue Λ k, tangentResiduePoint F⟩
  let leftReduction : leftObject ⟶ residueObject :=
    ⟨dualNumberToResidue Λ k, (tangentZero_spec F).1 _⟩
  let rightReduction : rightObject ⟶ residueObject :=
    ⟨dualNumberToResidue Λ k, (tangentZero_spec F).1 _⟩
  have pullbackExists := IsDeformationCategory.hasRimSchlessinger
    (p := CategoryOfElements.π F) |>.exists_pullback leftReduction rightReduction
      (dualNumberToResidue_surjective Λ k)
  let pullbackObject := pullbackExists.choose
  let leftProjection := pullbackExists.choose_spec.choose
  let rightProjection := pullbackExists.choose_spec.choose_spec.choose
  have basePullback := pullbackExists.choose_spec.choose_spec.choose_spec.2
  let comparison := tangentSelfPullbackLift leftProjection.val rightProjection.val
    basePullback.w
  exact F.map comparison pullbackObject.2

/-- The pair lift has the prescribed projections. -/
theorem tangentPairLift_spec (left right : F.obj (dualNumber Λ k)) :
    F.map (dualNumberSelfPullbackFst Λ) (tangentPairLift F left right) = left ∧
      F.map (dualNumberSelfPullbackSnd Λ) (tangentPairLift F left right) = right := sorry

/-- Addition is induced by summing the two infinitesimal coordinates. -/
def tangentAdd (left right : F.obj (dualNumber Λ k)) : F.obj (dualNumber Λ k) :=
  F.map (dualNumberAddHom Λ) (tangentPairLift F left right)

/-- Scalar multiplication is induced by scaling the infinitesimal coordinate. -/
def tangentScale (scalar : k) (value : F.obj (dualNumber Λ k)) :
    F.obj (dualNumber Λ k) :=
  F.map (dualNumberScaleHom Λ scalar) value

/-- The dual-number addition and negation operations satisfy the abelian-group laws. -/
theorem tangentAdd_laws :
    (∀ left middle right, tangentAdd F (tangentAdd F left middle) right =
      tangentAdd F left (tangentAdd F middle right)) ∧
    (∀ left right, tangentAdd F left right = tangentAdd F right left) ∧
    (∀ value, tangentAdd F (tangentZero F) value = value) ∧
    (∀ value, tangentAdd F value (tangentZero F) = value) ∧
    (∀ value, tangentAdd F (tangentScale F (-1) value) value = tangentZero F) := sorry

/-- Tangent vectors of a deformation functor form an abelian group under the canonical
dual-number operations. -/
instance instAddCommGroupTangent : AddCommGroup (F.obj (dualNumber Λ k)) where
  add := tangentAdd F
  zero := tangentZero F
  neg := tangentScale F (-1)
  nsmul := @nsmulRec _ ⟨tangentZero F⟩ ⟨tangentAdd F⟩
  zsmul := @zsmulRec _ ⟨tangentZero F⟩ ⟨tangentAdd F⟩ ⟨tangentScale F (-1)⟩
    (@nsmulRec _ ⟨tangentZero F⟩ ⟨tangentAdd F⟩)
  add_assoc := (tangentAdd_laws F).1
  add_comm := (tangentAdd_laws F).2.1
  zero_add := (tangentAdd_laws F).2.2.1
  add_zero := (tangentAdd_laws F).2.2.2.1
  neg_add_cancel := (tangentAdd_laws F).2.2.2.2

/-- Dual-number scaling satisfies the vector-space laws. -/
theorem tangentScale_laws :
    (∀ value, tangentScale F 1 value = value) ∧
    (∀ left right value, tangentScale F (left * right) value =
      tangentScale F left (tangentScale F right value)) ∧
    (∀ scalar left right, tangentScale F scalar (left + right) =
      tangentScale F scalar left + tangentScale F scalar right) ∧
    (∀ scalar, tangentScale F scalar 0 = 0) ∧
    (∀ left right value, tangentScale F (left + right) value =
      tangentScale F left value + tangentScale F right value) ∧
    (∀ value, tangentScale F 0 value = 0) := sorry

/-- The dual-number scaling operation equips tangent vectors with their canonical
residue-field module structure. -/
instance instModuleTangent : Module k (F.obj (dualNumber Λ k)) where
  smul := tangentScale F
  one_smul := (tangentScale_laws F).1
  mul_smul := (tangentScale_laws F).2.1
  smul_add := (tangentScale_laws F).2.2.1
  smul_zero := (tangentScale_laws F).2.2.2.1
  add_smul := (tangentScale_laws F).2.2.2.2.1
  zero_smul := (tangentScale_laws F).2.2.2.2.2

variable {F} {targetFunctor : ArtinianLocalAlgCat Λ k ⥤ Type v}
  [IsDeformationCategory (CategoryOfElements.π targetFunctor)]

/-- Natural transformations preserve tangent addition and scalar multiplication. -/
theorem tangentMap_laws (transformation : F ⟶ targetFunctor) :
    (∀ left right : F.obj (dualNumber Λ k),
      transformation.app (dualNumber Λ k) (left + right) =
        transformation.app (dualNumber Λ k) left + transformation.app (dualNumber Λ k) right) ∧
    (∀ (scalar : k) (value : F.obj (dualNumber Λ k)),
      transformation.app (dualNumber Λ k) (scalar • value) =
        scalar • transformation.app (dualNumber Λ k) value) := sorry

/-- The differential of a natural transformation is its dual-number component. -/
def tangentMap (transformation : F ⟶ targetFunctor) :
    F.obj (dualNumber Λ k) →ₗ[k] targetFunctor.obj (dualNumber Λ k) where
  toFun := transformation.app (dualNumber Λ k)
  map_add' := (tangentMap_laws transformation).1
  map_smul' := (tangentMap_laws transformation).2

/-- Evaluating the tangent map gives the supplied natural-transformation component. -/
theorem tangentMap_apply (transformation : F ⟶ targetFunctor) (value : F.obj (dualNumber Λ k)) :
    tangentMap transformation value = transformation.app (dualNumber Λ k) value := rfl

end CategoryTheory.Functor
