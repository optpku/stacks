/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Integral closure of the structure sheaf in a quasi-coherent algebra

On the small étale site of an algebraic space, the integral closure of `𝒪_X` in a
quasi-coherent `𝒪_X`-algebra `A` is the sheaf whose sections over `U` are the elements of
`A(U)` that become integral after restriction along some covering family.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- A section of a quasi-coherent `𝒪_X`-algebra over an étale object is locally integral if it
becomes integral after restriction along some covering family in the small étale precoverage. -/
def IsLocallyIntegral {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) (a : sectionRing A U) : Prop :=
  ∃ R : Presieve U, R ∈ smallEtalePrecoverage X U ∧
    ∀ ⦃V : smallEtaleSite X⦄ (f : V ⟶ U), R f →
      _root_.IsIntegral Γ(V.left.left, ⊤) ((A.obj.right.obj.map f.op).hom a)

/-- The subalgebra of locally integral sections of `A` over an étale object `U`. -/
def locallyIntegral {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) : Subalgebra Γ(U.left.left, ⊤) (sectionRing A U) where
  carrier := { a | IsLocallyIntegral A U a }
  add_mem' := sorry
  mul_mem' := sorry
  algebraMap_mem' := sorry

/-- Membership in `locallyIntegral A U` is local integrality of the section. -/
theorem locallyIntegral_mem_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) {a : sectionRing A U} :
    a ∈ locallyIntegral A U ↔ IsLocallyIntegral A U a :=
  sorry

/-- Restriction along a morphism of étale objects preserves locally integral sections. -/
theorem locallyIntegral_map_mem {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    ∀ ⦃a : sectionRing A U⦄, a ∈ locallyIntegral A U →
      (A.obj.right.obj.map f.op).hom a ∈ locallyIntegral A V :=
  sorry

/-- The presheaf of locally integral sections of a quasi-coherent `𝒪_X`-algebra. -/
def integralClosureFunctor {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (locallyIntegral A U.unop)
  map {U V} f :=
    CommRingCat.ofHom
      (RingHom.restrict (A.obj.right.obj.map f).hom (locallyIntegral A U.unop)
        (locallyIntegral A V.unop) (locallyIntegral_map_mem A f.unop))
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The presheaf of locally integral sections is a sheaf on the small étale site. -/
theorem integralClosureFunctor_isSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    Presheaf.IsSheaf (smallEtaleTopology X) (integralClosureFunctor A) :=
  sorry

/-- The sheaf of locally integral sections of a quasi-coherent `𝒪_X`-algebra. -/
def integralClosureSheaf {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} where
  obj := integralClosureFunctor A
  property := integralClosureFunctor_isSheaf A

/-- The structure morphism from `𝒪_X` to the sheaf of locally integral sections of `A`. -/
def integralClosureStructure {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    commRingStructureSheaf X ⟶ integralClosureSheaf A :=
  InducedCategory.homMk
    { app := fun U ↦
        CommRingCat.ofHom (algebraMap Γ(U.unop.left.left, ⊤) (locallyIntegral A U.unop))
      naturality := sorry }

/-- The quasi-coherent `𝒪_X`-subalgebra of `A` obtained by taking locally integral sections. -/
def integralClosure {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    X.QcAlgebraUnder where
  obj := Under.mk (integralClosureStructure A)
  property := sorry

/-- The inclusion of locally integral sections, as a morphism of sheaves of algebras. -/
def inclusionRight {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (integralClosure A).obj.right ⟶ A.obj.right :=
  InducedCategory.homMk
    { app := fun U ↦ CommRingCat.ofHom (locallyIntegral A U.unop).val.toRingHom
      naturality := sorry }

/-- The structure morphism of `integralClosure A` factors as the inclusion into `A`. -/
theorem inclusionRight_w {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (integralClosure A).obj.hom ≫ inclusionRight A = A.obj.hom :=
  sorry

/-- The inclusion `integralClosure A ⟶ A` of quasi-coherent `𝒪_X`-algebras. -/
def inclusion {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    integralClosure A ⟶ A :=
  InducedCategory.homMk (Under.homMk (inclusionRight A) (inclusionRight_w A))

/-- On sections, the inclusion `integralClosure A ⟶ A` is the subtype inclusion of locally
integral sections. -/
theorem inclusion_app {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) :
    (InducedCategory.Hom.hom ((forget X).map (inclusion A)).right).app (op U) =
      CommRingCat.ofHom (locallyIntegral A U).val.toRingHom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
