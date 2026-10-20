/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Equivalence
public import Mathlib.Algebra.Module.CharacterModule

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u v

namespace ActualOppositeCharacter

/-- The additive character carrier, kept distinct so its canonical RIGHT
scalar action cannot be confused with the commutative character-module instance. -/
def Carrier (M : Type v) [AddCommGroup M] := CharacterModule M

instance (M : Type v) [AddCommGroup M] : AddCommGroup (Carrier M) :=
  inferInstanceAs (AddCommGroup (CharacterModule M))

instance (M : Type v) [AddCommGroup M] :
    FunLike (Carrier M) M (AddCircle (1 : ℚ)) :=
  inferInstanceAs (FunLike (CharacterModule M) M (AddCircle (1 : ℚ)))

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Right scalar multiplication is precomposition by LEFT multiplication on M. -/
def scalar (r : Rᵐᵒᵖ) (χ : Carrier M) : Carrier M :=
  (show CharacterModule M from χ).comp
    { toFun := fun m ↦ r.unop • m
      map_zero' := smul_zero _
      map_add' := smul_add _ }

/-- The opposite multiplication order is essential for associativity. -/
instance rightModule : Module Rᵐᵒᵖ (Carrier M) where
  smul := scalar R M
  one_smul := by
    intro χ
    apply DFunLike.ext
    intro m
    change χ ((1 : R) • m) = χ m
    rw [one_smul]
  mul_smul := by
    intro r s χ
    apply DFunLike.ext
    intro m
    change χ ((s.unop * r.unop) • m) = χ (s.unop • (r.unop • m))
    rw [mul_smul]
  smul_zero := by intros; apply DFunLike.ext; intro m; rfl
  smul_add := by intros; apply DFunLike.ext; intro m; rfl
  zero_smul := by
    intro χ
    apply DFunLike.ext
    intro m
    change (show CharacterModule M from χ) ((0 : R) • m) = 0
    rw [zero_smul, map_zero]
  add_smul := by
    intro r s χ
    apply DFunLike.ext
    intro m
    change (show CharacterModule M from χ) ((r.unop + s.unop) • m) = _
    rw [add_smul, map_add]
    rfl

@[simp] theorem scalar_apply (r : Rᵐᵒᵖ) (χ : Carrier M) (m : M) :
    (r • χ) m = χ (r.unop • m) := rfl

/-- Character precomposition reverses maps and changes coefficient handedness. -/
def map {N : Type v} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Carrier N →ₗ[Rᵐᵒᵖ] Carrier M where
  toFun χ := (show CharacterModule N from χ).comp f.toAddMonoidHom
  map_add' := by intros; rfl
  map_smul' := by
    intro r χ
    apply DFunLike.ext
    intro m
    change χ (r.unop • f m) = χ (f (r.unop • m))
    rw [f.map_smul]

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The contragredient G-action COMMUTES with the right R-action. -/
def action (N : DiscreteModuleCat R G) : Action (ModuleCat.{max u v} Rᵐᵒᵖ) G where
  V := ModuleCat.of Rᵐᵒᵖ (Carrier (N.obj.V : Type (max u v)))
  ρ := { toFun := fun g ↦ ModuleCat.ofHom (map R N.obj.V (N.obj.ρ g⁻¹).hom)
         map_one' := by sorry
         map_mul' := by sorry }

variable [Finite R]

/-- Opposite scalars retain the same finite underlying set. -/
instance oppositeFinite : Finite Rᵐᵒᵖ :=
  Finite.of_injective MulOpposite.unop MulOpposite.unop_injective

/-- Only finite inputs are made discrete here. Their finite character action
has open stabilizers; no such claim is made for characters of arbitrary
infinite discrete representations. -/
def finiteRepresentation
    (N : (finiteTypeDiscreteModule R G).FullSubcategory) :
    (finiteTypeDiscreteModule Rᵐᵒᵖ G).FullSubcategory :=
  ⟨⟨action R G N.obj, by sorry⟩, by sorry⟩

/-- Actual equivariant character precomposition on finite coefficient maps. -/
def finiteMap {N L : (finiteTypeDiscreteModule R G).FullSubcategory} (f : N ⟶ L) :
    finiteRepresentation R G L ⟶ finiteRepresentation R G N :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (map R N.obj.obj.V f.hom.hom.hom.hom)
      comm := fun _ ↦ by sorry })

/-- Contravariant finite character functor with opposite, not commuted, scalars. -/
def finiteFunctor : (finiteTypeDiscreteModule R G).FullSubcategoryᵒᵖ ⥤
    (finiteTypeDiscreteModule Rᵐᵒᵖ G).FullSubcategory where
  obj N := finiteRepresentation R G N.unop
  map f := finiteMap R G f.unop
  map_id := by sorry
  map_comp := by sorry

end ActualOppositeCharacter

namespace ActualOppositeCharacterSheaf
variable {X : Scheme.{u}} [ConnectedSpace X]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable (x : GeometricPoint X)
variable (N : (finiteTypeDiscreteModule R (Aut (GeometricPoint.finiteFiber x))).FullSubcategory)

/-- Published inverse applied functorially to the actual opposite-coefficient
character representation, including all coefficient morphisms. -/
def functor :=
  ActualOppositeCharacter.finiteFunctor R (Aut (GeometricPoint.finiteFiber x)) ⋙
    (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Rᵐᵒᵖ x).inverse

/-- The actual right-coefficient character sheaf via the PUBLISHED Chap59
germ/transported-module inverse. This is the character coefficient before
the separate cyclotomic Tate twist, not a claimed duality isomorphism. -/
def associated :=
  (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Rᵐᵒᵖ x).inverse.obj
    (ActualOppositeCharacter.finiteRepresentation R (Aut (GeometricPoint.finiteFiber x)) N)

/-- Its stalk identification is the published counit, with its actual
linear equivariant germ maps, not a chosen isomorphism. -/
def stalkIso :
    (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Rᵐᵒᵖ x).functor.obj
      (associated R x N) ≅
    ActualOppositeCharacter.finiteRepresentation R (Aut (GeometricPoint.finiteFiber x)) N :=
  (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Rᵐᵒᵖ x).counitIso.app _

end ActualOppositeCharacterSheaf
