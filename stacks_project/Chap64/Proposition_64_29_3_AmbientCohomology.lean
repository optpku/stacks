/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Injective
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat

noncomputable section

universe u v

namespace AmbientDiscreteCohomology

variable (Λ : Type u) [CommRing Λ]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Invariants on ALL discrete continuous modules, before imposing finiteness
on the input. -/
def invariants : DiscreteModuleCat Λ G ⥤ ModuleCat.{max u v} Λ :=
  (openStabilizer Λ G).ι ⋙ Rep.ActionToRep Λ G ⋙ Rep.invariantsFunctor Λ G

instance : (invariants Λ G).Additive where
  map_add := by intros; rfl

/-- Use the existing cofree/coreflection embedding; do not invent finite
injectives. -/
def injectivePresentation (M : DiscreteModuleCat Λ G) : InjectivePresentation M :=
  HasFunctorialInjectives.presentation M

/-- The ambient category admits resolutions through its canonical embeddings. -/
example : HasInjectiveResolutions (DiscreteModuleCat Λ G) := inferInstance

/-- Continuous cohomology as right-derived invariants in the ambient category. -/
def cohomology (i : ℕ) : DiscreteModuleCat Λ G ⥤ ModuleCat.{max u v} Λ :=
  (invariants Λ G).rightDerived i

/-- Actual canonical resolution comparison, usable on finite inputs without
ever requiring the resolution terms to be finite. -/
def resolutionIso (M : DiscreteModuleCat Λ G) (I : InjectiveResolution M) (i : ℕ) :
    (cohomology Λ G i).obj M ≅
      (HomologicalComplex.homologyFunctor _ _ i).obj
        (((invariants Λ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (invariants Λ G) i

/-- The trivial action on any coefficient module is discrete continuous. -/
def trivial : ModuleCat.{max u v} Λ ⥤ DiscreteModuleCat Λ G where
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
def invariantsUnit : 𝟭 (ModuleCat.{max u v} Λ) ⟶ trivial Λ G ⋙ invariants Λ G where
  app V := ModuleCat.ofHom
    { toFun := fun v ↦ ⟨v, fun _ ↦ rfl⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality := fun _ _ _ ↦ rfl

/-- The counit is the actual invariant-submodule inclusion into the action. -/
def invariantsCounit : invariants Λ G ⋙ trivial Λ G ⟶ 𝟭 (DiscreteModuleCat Λ G) where
  app M := ObjectProperty.homMk
    { hom := ModuleCat.ofHom (Submodule.subtype _)
      comm := fun g ↦ by
        ext x
        exact (x.property g).symm }
  naturality := fun _ _ _ ↦ rfl

/-- Trivial actions are left adjoint to invariants on all continuous discrete modules. -/
def invariantsAdjunction : trivial Λ G ⊣ invariants Λ G where
  unit := invariantsUnit Λ G
  counit := invariantsCounit Λ G
  left_triangle_components := fun _ ↦ rfl
  right_triangle_components := fun _ ↦ rfl

/-- Ambient invariants are a right adjoint through the explicit inclusion counit. -/
instance invariants_isRightAdjoint : (invariants Λ G).IsRightAdjoint :=
  (invariantsAdjunction Λ G).isRightAdjoint

/-- The degree-zero comparison is Mathlib's canonical inverse of the derived unit. -/
def zeroIso : cohomology Λ G 0 ≅ invariants Λ G :=
  (invariants Λ G).rightDerivedZeroIsoSelf

/-- The forward derived unit, constructed using the ambient injective resolution. -/
def degreeZeroUnit : invariants Λ G ⟶ cohomology Λ G 0 :=
  (invariants Λ G).toRightDerivedZero

/-- The inverse comparison is the actual derived unit, rather than a zero map. -/
theorem zeroIso_inv : (zeroIso Λ G).inv = degreeZeroUnit Λ G := rfl

/-- The two canonical degree-zero maps compose to the identity on cohomology. -/
theorem zeroIso_hom_unit :
    (zeroIso Λ G).hom ≫ degreeZeroUnit Λ G = 𝟙 (cohomology Λ G 0) :=
  (zeroIso Λ G).hom_inv_id

/-- The two canonical degree-zero maps compose to the identity on invariants. -/
theorem zeroIso_unit_hom :
    degreeZeroUnit Λ G ≫ (zeroIso Λ G).hom = 𝟙 (invariants Λ G) :=
  (zeroIso Λ G).inv_hom_id

end AmbientDiscreteCohomology
