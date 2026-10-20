/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.LinearMap.Prod
public import Mathlib.Algebra.Module.TransferInstance
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Functor
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid
public import ReasLib.CategoryTheory.Groupoid.Quotient
public import ReasLib.CategoryTheory.Fibered.InfinitesimalAutomorphisms

/-!
# Deformation invariants of smooth groupoid quotients

The quotient of a smooth groupoid of deformation functors is a deformation category.
Its tangent space is the cokernel of the difference of the source and target
differentials, and its infinitesimal automorphisms form the kernel of their product.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor Fiber

universe u w

namespace CategoryTheory.GroupoidInFunctors

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))

/-- The quotient of a smooth groupoid of deformation functors is a deformation category. -/
instance instIsDeformationCategory_quotient
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)] :
    Functor.IsDeformationCategory G.quotient.p := sorry

variable [IsSmooth G.s G.t]
  [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
  [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]

/-- The quotient is a predeformation category satisfying the Rim-Schlessinger condition. -/
theorem isDeformationCategory_quotient_spec :
    Functor.IsPredeformationCategory G.quotient.p ∧
      Functor.HasRimSchlessinger G.quotient.p :=
  ⟨inferInstance, Functor.IsDeformationCategory.hasRimSchlessinger⟩

/-- A dual-number point defines an explicit object in the quotient fibre. -/
def tangentSpaceQuotientFiber (value : G.U.obj (dualNumber Λ k)) :
    G.quotient.p.Fiber (dualNumber Λ k) :=
  Functor.Fiber.mk (a := Functor.ofGroupoidValued.mkObj G.toFunctor
    (dualNumber Λ k) value) rfl

/-- The explicit fibre object projects to the dual-number algebra. -/
theorem tangentSpaceQuotientFiber_over (value : G.U.obj (dualNumber Λ k)) :
    G.quotient.p.obj (fiberInclusion.obj (tangentSpaceQuotientFiber G value)) =
      dualNumber Λ k := rfl

/-- A fibre object's component transported along its base equality is a dual-number point. -/
def tangentRepresentative (fiberObject : G.quotient.p.Fiber (dualNumber Λ k)) :
    G.U.obj (dualNumber Λ k) :=
  G.U.map (eqToHom fiberObject.property) fiberObject.val.fiber

/-- A dual-number object determines its canonical quotient tangent class. -/
def tangentSpaceQuotientMk (value : G.U.obj (dualNumber Λ k)) :
    Functor.tangentSpace G.quotient.p :=
  Functor.tangentSpace.mk G.quotient.p (tangentSpaceQuotientFiber G value)

/-- The quotient tangent map sends a point to the class of its explicit fibre object. -/
theorem tangentSpaceQuotientMk_apply (value : G.U.obj (dualNumber Λ k)) :
    tangentSpaceQuotientMk G value =
      Quotient.mk (isIsomorphicSetoid _) (tangentSpaceQuotientFiber G value) := rfl

/-- Every quotient tangent vector has an object-functor representative. -/
theorem tangentSpaceQuotientMk_surjective :
    Function.Surjective (tangentSpaceQuotientMk G) := sorry

/-- Two points determine the same quotient tangent class exactly when an arrow connects them. -/
theorem tangentSpaceQuotientMk_eq_iff (left right : G.U.obj (dualNumber Λ k)) :
    tangentSpaceQuotientMk G left = tangentSpaceQuotientMk G right ↔
      Nonempty (G.PointHom (dualNumber Λ k) left right) := sorry

/-- Addition and scaling of representatives are invariant under fibre isomorphism. -/
theorem tangentSpaceQuotient_operations_wellDefined :
    (∀ left left' right right' : G.quotient.p.Fiber (dualNumber Λ k),
      Nonempty (left ≅ left') → Nonempty (right ≅ right') →
      tangentSpaceQuotientMk G (tangentRepresentative G left + tangentRepresentative G right) =
        tangentSpaceQuotientMk G (tangentRepresentative G left' + tangentRepresentative G right')) ∧
    (∀ (scalar : k) (left right : G.quotient.p.Fiber (dualNumber Λ k)),
      Nonempty (left ≅ right) →
      tangentSpaceQuotientMk G (scalar • tangentRepresentative G left) =
        tangentSpaceQuotientMk G (scalar • tangentRepresentative G right)) := sorry

/-- Addition on quotient tangent classes descends addition of object representatives. -/
def tangentSpaceQuotientAdd :
    Functor.tangentSpace G.quotient.p → Functor.tangentSpace G.quotient.p →
      Functor.tangentSpace G.quotient.p :=
  Quotient.lift₂
    (fun left right ↦ tangentSpaceQuotientMk G
      (tangentRepresentative G left + tangentRepresentative G right))
    (fun left right left' right' leftIso rightIso ↦
      (tangentSpaceQuotient_operations_wellDefined G).1 left left' right right' leftIso rightIso)

/-- Scaling on quotient tangent classes descends scaling of object representatives. -/
def tangentSpaceQuotientScale (scalar : k) :
    Functor.tangentSpace G.quotient.p → Functor.tangentSpace G.quotient.p :=
  Quotient.lift
    (fun fiberObject ↦ tangentSpaceQuotientMk G (scalar • tangentRepresentative G fiberObject))
    ((tangentSpaceQuotient_operations_wellDefined G).2 scalar)

/-- The descended operations obey the abelian-group laws. -/
theorem tangentSpaceQuotient_additive_laws :
    (∀ left middle right, tangentSpaceQuotientAdd G (tangentSpaceQuotientAdd G left middle) right =
      tangentSpaceQuotientAdd G left (tangentSpaceQuotientAdd G middle right)) ∧
    (∀ left right, tangentSpaceQuotientAdd G left right = tangentSpaceQuotientAdd G right left) ∧
    (∀ value, tangentSpaceQuotientAdd G (tangentSpaceQuotientMk G 0) value = value) ∧
    (∀ value, tangentSpaceQuotientAdd G value (tangentSpaceQuotientMk G 0) = value) ∧
    (∀ value, tangentSpaceQuotientAdd G (tangentSpaceQuotientScale G (-1) value) value =
      tangentSpaceQuotientMk G 0) := sorry

/-- The canonical tangent space of the quotient carries the descended abelian-group structure. -/
instance instAddCommGroupQuotientTangent : AddCommGroup (Functor.tangentSpace G.quotient.p) where
  add := tangentSpaceQuotientAdd G
  zero := tangentSpaceQuotientMk G 0
  neg := tangentSpaceQuotientScale G (-1)
  nsmul := @nsmulRec _ ⟨tangentSpaceQuotientMk G 0⟩ ⟨tangentSpaceQuotientAdd G⟩
  zsmul := @zsmulRec _ ⟨tangentSpaceQuotientMk G 0⟩ ⟨tangentSpaceQuotientAdd G⟩
    ⟨tangentSpaceQuotientScale G (-1)⟩
    (@nsmulRec _ ⟨tangentSpaceQuotientMk G 0⟩ ⟨tangentSpaceQuotientAdd G⟩)
  add_assoc := (tangentSpaceQuotient_additive_laws G).1
  add_comm := (tangentSpaceQuotient_additive_laws G).2.1
  zero_add := (tangentSpaceQuotient_additive_laws G).2.2.1
  add_zero := (tangentSpaceQuotient_additive_laws G).2.2.2.1
  neg_add_cancel := (tangentSpaceQuotient_additive_laws G).2.2.2.2

/-- Descended scaling satisfies the residue-field module laws. -/
theorem tangentSpaceQuotient_scalar_laws :
    (∀ value, tangentSpaceQuotientScale G 1 value = value) ∧
    (∀ left right value, tangentSpaceQuotientScale G (left * right) value =
      tangentSpaceQuotientScale G left (tangentSpaceQuotientScale G right value)) ∧
    (∀ scalar left right, tangentSpaceQuotientScale G scalar (left + right) =
      tangentSpaceQuotientScale G scalar left + tangentSpaceQuotientScale G scalar right) ∧
    (∀ scalar, tangentSpaceQuotientScale G scalar 0 = 0) ∧
    (∀ left right value, tangentSpaceQuotientScale G (left + right) value =
      tangentSpaceQuotientScale G left value + tangentSpaceQuotientScale G right value) ∧
    (∀ value, tangentSpaceQuotientScale G 0 value = 0) := sorry

/-- The canonical quotient tangent space carries the descended residue-field module structure. -/
instance instModuleQuotientTangent : Module k (Functor.tangentSpace G.quotient.p) where
  smul := tangentSpaceQuotientScale G
  one_smul := (tangentSpaceQuotient_scalar_laws G).1
  mul_smul := (tangentSpaceQuotient_scalar_laws G).2.1
  smul_add := (tangentSpaceQuotient_scalar_laws G).2.2.1
  smul_zero := (tangentSpaceQuotient_scalar_laws G).2.2.2.1
  add_smul := (tangentSpaceQuotient_scalar_laws G).2.2.2.2.1
  zero_smul := (tangentSpaceQuotient_scalar_laws G).2.2.2.2.2

/-- The canonical map to quotient tangent classes is linear. -/
theorem tangentSpaceQuotientMk_linear :
    (∀ left right, tangentSpaceQuotientMk G (left + right) =
      tangentSpaceQuotientMk G left + tangentSpaceQuotientMk G right) ∧
    (∀ (scalar : k) value, tangentSpaceQuotientMk G (scalar • value) =
      scalar • tangentSpaceQuotientMk G value) := sorry

/-- The linear canonical map from object tangent vectors to quotient tangent vectors. -/
def tangentSpaceQuotientMkLinear :
    G.U.obj (dualNumber Λ k) →ₗ[k] Functor.tangentSpace G.quotient.p where
  toFun := tangentSpaceQuotientMk G
  map_add' := (tangentSpaceQuotientMk_linear G).1
  map_smul' := (tangentSpaceQuotientMk_linear G).2

/-- The source differential is the source natural transformation on dual numbers. -/
def tangentSource : G.R.obj (dualNumber Λ k) →ₗ[k] G.U.obj (dualNumber Λ k) :=
  Functor.tangentMap G.s

/-- The target differential is the target natural transformation on dual numbers. -/
def tangentTarget : G.R.obj (dualNumber Λ k) →ₗ[k] G.U.obj (dualNumber Λ k) :=
  Functor.tangentMap G.t

/-- The canonical tangent map descends to the cokernel, and representatives descend to its inverse. -/
theorem tangentCokernel_wellDefined :
    (∀ left right : G.U.obj (dualNumber Λ k),
      (LinearMap.range (tangentSource G - tangentTarget G)).quotientRel left right →
      tangentSpaceQuotientMk G left = tangentSpaceQuotientMk G right) ∧
    (∀ left right : G.quotient.p.Fiber (dualNumber Λ k), Nonempty (left ≅ right) →
      (Submodule.Quotient.mk (tangentRepresentative G left) :
        G.U.obj (dualNumber Λ k) ⧸ LinearMap.range (tangentSource G - tangentTarget G)) =
      Submodule.Quotient.mk (tangentRepresentative G right)) := sorry

/-- The cokernel class maps to the canonical quotient tangent class. -/
def tangentCokernelToTangent :
    (G.U.obj (dualNumber Λ k) ⧸ LinearMap.range (tangentSource G - tangentTarget G)) →
      Functor.tangentSpace G.quotient.p :=
  Quotient.lift (tangentSpaceQuotientMk G) (tangentCokernel_wellDefined G).1

/-- A quotient tangent class maps to the cokernel class of its transported representative. -/
def tangentToCokernel : Functor.tangentSpace G.quotient.p →
    G.U.obj (dualNumber Λ k) ⧸ LinearMap.range (tangentSource G - tangentTarget G) :=
  Quotient.lift (fun fiberObject ↦ Submodule.Quotient.mk (tangentRepresentative G fiberObject))
    (tangentCokernel_wellDefined G).2

/-- The explicit cokernel maps are mutually inverse and the forward map is linear. -/
theorem tangentCokernel_inverse_laws :
    Function.LeftInverse (tangentToCokernel G) (tangentCokernelToTangent G) ∧
    Function.RightInverse (tangentToCokernel G) (tangentCokernelToTangent G) ∧
    (∀ left right, tangentCokernelToTangent G (left + right) =
      tangentCokernelToTangent G left + tangentCokernelToTangent G right) ∧
    (∀ (scalar : k) value, tangentCokernelToTangent G (scalar • value) =
      scalar • tangentCokernelToTangent G value) := sorry

/-- The tangent space of a smooth groupoid quotient is the cokernel of the difference
of its source and target differentials. -/
def tangentSpace_quotient :
    (G.U.obj (dualNumber Λ k) ⧸ LinearMap.range (tangentSource G - tangentTarget G)) ≃ₗ[k]
      Functor.tangentSpace G.quotient.p where
  toFun := tangentCokernelToTangent G
  invFun := tangentToCokernel G
  left_inv := (tangentCokernel_inverse_laws G).1
  right_inv := (tangentCokernel_inverse_laws G).2.1
  map_add' := (tangentCokernel_inverse_laws G).2.2.1
  map_smul' := (tangentCokernel_inverse_laws G).2.2.2

/-- The cokernel equivalence maps the class of a point to its canonical tangent class. -/
theorem tangentSpace_quotient_apply (value : G.U.obj (dualNumber Λ k)) :
    tangentSpace_quotient G (Submodule.Quotient.mk value) =
      tangentSpaceQuotientMk G value := rfl

/-- A residue point gives the trivial dual-number object by the constant-coefficient inclusion. -/
def origin (residuePoint : G.U.obj (residue Λ k)) : G.U.obj (dualNumber Λ k) :=
  G.U.map (residueToDualNumber Λ k) residuePoint

/-- The origin evaluates to the constant-coefficient pushforward of the residue point. -/
theorem origin_apply (residuePoint : G.U.obj (residue Λ k)) :
    origin G residuePoint = G.U.map (residueToDualNumber Λ k) residuePoint := rfl

/-- The residue point determines an explicit object in the quotient residue fibre. -/
def quotientResidueFiber (residuePoint : G.U.obj (residue Λ k)) :
    G.quotient.p.Fiber (residue Λ k) :=
  Functor.Fiber.mk (a := Functor.ofGroupoidValued.mkObj G.toFunctor (residue Λ k) residuePoint) rfl

/-- The trivial object is the tangent zero and reduces to its supplied residue point. -/
theorem quotientOriginReduction_laws (residuePoint : G.U.obj (residue Λ k)) :
    origin G residuePoint = (0 : G.U.obj (dualNumber Λ k)) ∧
      G.U.map (dualNumberToResidue Λ k) (origin G residuePoint) = residuePoint := sorry

/-- The origin reduces to the residue object through the base projection and an identity arrow. -/
def quotientOriginReduction (residuePoint : G.U.obj (residue Λ k)) :
    fiberInclusion.obj (tangentSpaceQuotientFiber G (origin G residuePoint)) ⟶
      fiberInclusion.obj (quotientResidueFiber G residuePoint) :=
  Functor.ofGroupoidValued.mkHom G.toFunctor (dualNumberToResidue Λ k)
    (eqToHom (quotientOriginReduction_laws G residuePoint).2 ≫
      PointHom.id G (residue Λ k) residuePoint)

/-- The explicit origin reduction lifts the dual-number residue projection. -/
instance instIsHomLiftQuotientOriginReduction (residuePoint : G.U.obj (residue Λ k)) :
    G.quotient.p.IsHomLift (dualNumberToResidue Λ k) (quotientOriginReduction G residuePoint) :=
  IsHomLift.of_fac G.quotient.p _ _ rfl rfl (by
    change dualNumberToResidue Λ k = 𝟙 _ ≫ dualNumberToResidue Λ k ≫ 𝟙 _
    simp)

/-- The infinitesimal automorphisms are the canonical relative subgroup fixing the origin reduction. -/
def infAutQuotient (residuePoint : G.U.obj (residue Λ k)) :=
  Functor.infinitesimalAut G.quotient.p (dualNumberToResidue Λ k)
    (quotientOriginReduction G residuePoint)

/-- An infinitesimal automorphism gives its underlying arrow of the arrow functor. -/
def infAutQuotient_arrow (residuePoint : G.U.obj (residue Λ k))
    (automorphism : infAutQuotient G residuePoint) : G.R.obj (dualNumber Λ k) :=
  automorphism.val.hom.val.fiber.arrow

/-- The underlying arrow of an infinitesimal automorphism has both endpoints at the tangent origin. -/
theorem infAutQuotient_arrow_spec (residuePoint : G.U.obj (residue Λ k))
    (automorphism : infAutQuotient G residuePoint) :
    G.s.app (dualNumber Λ k) (infAutQuotient_arrow G residuePoint automorphism) =
      origin G residuePoint ∧
    G.t.app (dualNumber Λ k) (infAutQuotient_arrow G residuePoint automorphism) =
      origin G residuePoint := sorry

/-- An arrow with specified endpoints gives an explicit vertical-base endomorphism of the origin. -/
def quotientArrowHom (residuePoint : G.U.obj (residue Λ k))
    (arrow : G.R.obj (dualNumber Λ k))
    (source : G.s.app (dualNumber Λ k) arrow =
      G.U.map (𝟙 (dualNumber Λ k)) (origin G residuePoint))
    (target : G.t.app (dualNumber Λ k) arrow = origin G residuePoint) :
    fiberInclusion.obj (tangentSpaceQuotientFiber G (origin G residuePoint)) ⟶
      fiberInclusion.obj (tangentSpaceQuotientFiber G (origin G residuePoint)) :=
  Functor.ofGroupoidValued.mkHom G.toFunctor (𝟙 (dualNumber Λ k))
    (PointHom.ofArrow arrow source target)

/-- A kernel arrow and its supplied groupoid inverse have the required endpoints,
verticality, inverse identities, and reduction-fixing property. -/
theorem infAutQuotientOfArrow_laws (residuePoint : G.U.obj (residue Λ k))
    (arrow : LinearMap.ker ((tangentSource G).prod (tangentTarget G))) :
    ((G.s.app (dualNumber Λ k) arrow.val =
        G.U.map (𝟙 (dualNumber Λ k)) (origin G residuePoint)) ∧
      (G.t.app (dualNumber Λ k) arrow.val = origin G residuePoint) ∧
      (G.s.app (dualNumber Λ k) (G.i.app (dualNumber Λ k) arrow.val) =
        G.U.map (𝟙 (dualNumber Λ k)) (origin G residuePoint)) ∧
      (G.t.app (dualNumber Λ k) (G.i.app (dualNumber Λ k) arrow.val) =
        origin G residuePoint)) ∧
    (∀ (source : G.s.app (dualNumber Λ k) arrow.val =
          G.U.map (𝟙 (dualNumber Λ k)) (origin G residuePoint))
        (target : G.t.app (dualNumber Λ k) arrow.val = origin G residuePoint)
        (inverseSource : G.s.app (dualNumber Λ k) (G.i.app (dualNumber Λ k) arrow.val) =
          G.U.map (𝟙 (dualNumber Λ k)) (origin G residuePoint))
        (inverseTarget : G.t.app (dualNumber Λ k) (G.i.app (dualNumber Λ k) arrow.val) =
          origin G residuePoint),
      G.quotient.p.IsHomLift (𝟙 (dualNumber Λ k))
        (quotientArrowHom G residuePoint arrow.val source target) ∧
      G.quotient.p.IsHomLift (𝟙 (dualNumber Λ k))
        (quotientArrowHom G residuePoint (G.i.app (dualNumber Λ k) arrow.val)
          inverseSource inverseTarget) ∧
      (quotientArrowHom G residuePoint arrow.val source target ≫
        quotientArrowHom G residuePoint (G.i.app (dualNumber Λ k) arrow.val)
          inverseSource inverseTarget = 𝟙 _) ∧
      (quotientArrowHom G residuePoint (G.i.app (dualNumber Λ k) arrow.val)
          inverseSource inverseTarget ≫
        quotientArrowHom G residuePoint arrow.val source target = 𝟙 _) ∧
      (quotientArrowHom G residuePoint arrow.val source target ≫
        quotientOriginReduction G residuePoint = quotientOriginReduction G residuePoint)) := sorry

/-- A kernel arrow yields the origin automorphism with the supplied groupoid inverse. -/
def infAutQuotientOfArrow (residuePoint : G.U.obj (residue Λ k))
    (arrow : LinearMap.ker ((tangentSource G).prod (tangentTarget G))) :
    infAutQuotient G residuePoint := by
  let endpoints := (infAutQuotientOfArrow_laws G residuePoint arrow).1
  let forward := quotientArrowHom G residuePoint arrow.val endpoints.1 endpoints.2.1
  let backward := quotientArrowHom G residuePoint (G.i.app (dualNumber Λ k) arrow.val)
    endpoints.2.2.1 endpoints.2.2.2
  have laws := (infAutQuotientOfArrow_laws G residuePoint arrow).2
    endpoints.1 endpoints.2.1 endpoints.2.2.1 endpoints.2.2.2
  let ambientIso :
      fiberInclusion.obj (tangentSpaceQuotientFiber G (origin G residuePoint)) ≅
        fiberInclusion.obj (tangentSpaceQuotientFiber G (origin G residuePoint)) :=
    { hom := forward
      inv := backward
      hom_inv_id := laws.2.2.1
      inv_hom_id := laws.2.2.2.1 }
  exact ⟨Functor.Fiber.isoMk ambientIso laws.1, laws.2.2.2.2⟩

/-- The underlying arrow of an infinitesimal automorphism lies in the kernel of both differentials. -/
def infAutQuotientToKernel (residuePoint : G.U.obj (residue Λ k))
    (automorphism : infAutQuotient G residuePoint) :
    LinearMap.ker ((tangentSource G).prod (tangentTarget G)) := by
  refine ⟨infAutQuotient_arrow G residuePoint automorphism, ?_⟩
  change (G.s.app (dualNumber Λ k) (infAutQuotient_arrow G residuePoint automorphism),
    G.t.app (dualNumber Λ k) (infAutQuotient_arrow G residuePoint automorphism)) = (0, 0)
  exact Prod.ext
    ((infAutQuotient_arrow_spec G residuePoint automorphism).1.trans
      (quotientOriginReduction_laws G residuePoint).1)
    ((infAutQuotient_arrow_spec G residuePoint automorphism).2.trans
      (quotientOriginReduction_laws G residuePoint).1)

/-- Extraction of the arrow and construction of its origin automorphism are mutually inverse. -/
theorem infAutQuotientEquivKernel_laws (residuePoint : G.U.obj (residue Λ k)) :
    Function.LeftInverse (infAutQuotientOfArrow G residuePoint)
      (infAutQuotientToKernel G residuePoint) ∧
    Function.RightInverse (infAutQuotientOfArrow G residuePoint)
      (infAutQuotientToKernel G residuePoint) := sorry

/-- The explicit arrow comparison identifies infinitesimal automorphisms with the differential kernel. -/
def infAutQuotientEquivKernel (residuePoint : G.U.obj (residue Λ k)) :
    infAutQuotient G residuePoint ≃ LinearMap.ker ((tangentSource G).prod (tangentTarget G)) where
  toFun := infAutQuotientToKernel G residuePoint
  invFun := infAutQuotientOfArrow G residuePoint
  left_inv := (infAutQuotientEquivKernel_laws G residuePoint).1
  right_inv := (infAutQuotientEquivKernel_laws G residuePoint).2

/-- The explicit kernel comparison transports the canonical abelian-group operations. -/
instance instAddCommGroupInfAutQuotient (residuePoint : G.U.obj (residue Λ k)) :
    AddCommGroup (infAutQuotient G residuePoint) :=
  (infAutQuotientEquivKernel G residuePoint).addCommGroup

/-- The explicit kernel comparison transports the canonical residue-field scalar action. -/
instance instModuleInfAutQuotient (residuePoint : G.U.obj (residue Λ k)) :
    Module k (infAutQuotient G residuePoint) :=
  Equiv.module k (infAutQuotientEquivKernel G residuePoint)

/-- Infinitesimal automorphisms of the smooth quotient form the linear kernel of the
product of the source and target differentials. -/
def infinitesimalAutomorphisms_quotient (residuePoint : G.U.obj (residue Λ k)) :
    infAutQuotient G residuePoint ≃ₗ[k] LinearMap.ker ((tangentSource G).prod (tangentTarget G)) :=
  Equiv.linearEquiv k (infAutQuotientEquivKernel G residuePoint)

/-- The infinitesimal linear comparison returns the underlying groupoid arrow. -/
theorem infinitesimalAutomorphisms_quotient_apply (residuePoint : G.U.obj (residue Λ k))
    (automorphism : infAutQuotient G residuePoint) :
    (infinitesimalAutomorphisms_quotient G residuePoint automorphism).val =
      infAutQuotient_arrow G residuePoint automorphism := rfl

/-- Composition of infinitesimal automorphisms agrees with addition of their tangent arrows. -/
theorem infAutQuotient_mul_arrow (residuePoint : G.U.obj (residue Λ k))
    (left right : infAutQuotient G residuePoint) :
    infAutQuotient_arrow G residuePoint (left * right) =
      infAutQuotient_arrow G residuePoint left + infAutQuotient_arrow G residuePoint right := sorry

end CategoryTheory.GroupoidInFunctors
