/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Injective
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.CategoryTheory.Adjunction.Limits
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain

/-!
# Derived invariants of discrete continuous module actions

Invariant elements are taken in the category of all discrete continuous modules.
Its canonical injective embeddings define the right derived functors. The explicit
trivial-action adjunction supplies the degree-zero comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat

noncomputable section

universe u v

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

variable (R : Type u) [CommRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Invariants on ALL discrete continuous modules, before imposing finiteness
on the input. -/
def fixedPointsFunctor : DiscreteModuleCat R G ⥤ ModuleCat.{max u v} R :=
  (openStabilizer R G).ι ⋙ Rep.ActionToRep R G ⋙ Rep.invariantsFunctor R G

/-- The fixed-points functor on discrete continuous modules is additive. -/
instance fixedPointsFunctor_additive : (fixedPointsFunctor R G).Additive where
  map_add := by intros; rfl

/-- The fixed-points functor evaluates to the invariant submodule of the representation. -/
theorem fixedPointsFunctor_obj (M : DiscreteModuleCat R G) :
    (fixedPointsFunctor R G).obj M =
      ModuleCat.of R ((Rep.ActionToRep R G).obj M.obj).ρ.invariants := rfl

/-- Cohomology of discrete continuous modules as the right derived functor of invariants. -/
def derivedCohomologyFunctor (n : ℕ) : DiscreteModuleCat R G ⥤ ModuleCat.{max u v} R :=
  (fixedPointsFunctor R G).rightDerived n

/-- Actual canonical resolution comparison, usable on finite inputs without
ever requiring the resolution terms to be finite. -/
def derivedCohomologyResolutionIso (M : DiscreteModuleCat R G) (I : InjectiveResolution M) (i : ℕ) :
    (derivedCohomologyFunctor R G i).obj M ≅
      (HomologicalComplex.homologyFunctor _ _ i).obj
        (((fixedPointsFunctor R G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (fixedPointsFunctor R G) i

/-- The trivial action on any coefficient module is discrete continuous. -/
def trivialFunctor : ModuleCat.{max u v} R ⥤ DiscreteModuleCat R G where
  obj V := ⟨Action.trivial G V, by
    intro x
    have h : (MulAction.stabilizer G x : Set G) = Set.univ := by
      ext g
      simp [MulAction.mem_stabilizer_iff, Action.trivial]
      rfl
    rw [h]
    exact isOpen_univ⟩
  map f := ObjectProperty.homMk
    { hom := f
      comm := fun _ ↦ by
        change (𝟙 _) ≫ f = f ≫ (𝟙 _)
        simp }

/-- The unit includes a vector as an invariant vector of its trivial action. -/
def fixedPointsUnit : 𝟭 (ModuleCat.{max u v} R) ⟶ trivialFunctor R G ⋙ fixedPointsFunctor R G where
  app V := ModuleCat.ofHom
    { toFun := fun v ↦ ⟨v, fun _ ↦ rfl⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality := fun _ _ _ ↦ rfl

/-- The counit is the actual invariant-submodule inclusion into the action. -/
def fixedPointsCounit : fixedPointsFunctor R G ⋙ trivialFunctor R G ⟶ 𝟭 (DiscreteModuleCat R G) where
  app M := ObjectProperty.homMk
    { hom := ModuleCat.ofHom (Submodule.subtype _)
      comm := fun g ↦ by
        ext x
        exact (x.property g).symm }
  naturality := fun _ _ _ ↦ rfl

/-- Trivial actions are left adjoint to invariant elements on all discrete continuous modules. -/
def fixedPointsAdjunction : trivialFunctor R G ⊣ fixedPointsFunctor R G where
  unit := fixedPointsUnit R G
  counit := fixedPointsCounit R G
  left_triangle_components := fun _ ↦ rfl
  right_triangle_components := fun _ ↦ rfl

/-- The fixed-points functor is right adjoint through the explicit inclusion counit. -/
instance fixedPointsFunctor_isRightAdjoint : (fixedPointsFunctor R G).IsRightAdjoint :=
  (fixedPointsAdjunction R G).isRightAdjoint

/-- The degree-zero comparison is Mathlib's canonical inverse of the derived unit. -/
def derivedCohomologyZeroIso : derivedCohomologyFunctor R G 0 ≅ fixedPointsFunctor R G :=
  (fixedPointsFunctor R G).rightDerivedZeroIsoSelf

/-- The forward derived unit, constructed using the ambient injective resolution. -/
def toDerivedCohomologyZero : fixedPointsFunctor R G ⟶ derivedCohomologyFunctor R G 0 :=
  (fixedPointsFunctor R G).toRightDerivedZero

/-- The inverse of the degree-zero comparison is the derived unit. -/
theorem derivedCohomologyZeroIso_inv : (derivedCohomologyZeroIso R G).inv = toDerivedCohomologyZero R G := rfl

/-- The two canonical degree-zero maps compose to the identity on cohomology. -/
theorem derivedCohomologyZeroIso_hom_unit :
    (derivedCohomologyZeroIso R G).hom ≫ toDerivedCohomologyZero R G = 𝟙 (derivedCohomologyFunctor R G 0) :=
  (derivedCohomologyZeroIso R G).hom_inv_id

/-- The two canonical degree-zero maps compose to the identity on invariants. -/
theorem derivedCohomologyZeroIso_unit_hom :
    toDerivedCohomologyZero R G ≫ (derivedCohomologyZeroIso R G).hom = 𝟙 (fixedPointsFunctor R G) :=
  (derivedCohomologyZeroIso R G).inv_hom_id

/-- Invariants of discrete continuous integral modules, valued in abelian groups. -/
def invariantsFunctor : DiscreteModuleCat ℤ G ⥤ AddCommGrpCat.{v} :=
  fixedPointsFunctor ℤ G ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat

/-- The abelian-group-valued invariants functor is additive. -/
instance invariantsFunctor_additive : (invariantsFunctor G).Additive :=
  inferInstanceAs (fixedPointsFunctor ℤ G ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat).Additive

/-- Total right-derived invariants of discrete continuous integral modules. -/
abbrev derivedInvariants
    [CategoryWithHomology (DiscreteModuleCat ℤ G)]
    [HasDerivedCategory (DiscreteModuleCat ℤ G)]
    [Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived (invariantsFunctor G))
      (HomologicalComplex.quasiIso (DiscreteModuleCat ℤ G) (ComplexShape.up ℤ))] :
    DerivedCategory (DiscreteModuleCat ℤ G) ⥤ DerivedCategory AddCommGrpCat.{v} :=
  Functor.RightDerived.Cochain.functor (invariantsFunctor G)

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
