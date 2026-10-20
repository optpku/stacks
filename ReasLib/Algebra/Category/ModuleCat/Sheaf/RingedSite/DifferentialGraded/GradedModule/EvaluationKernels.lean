module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.LeftExact

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
noncomputable section
universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}} (A : DGA(O))

/-- Evaluation is the stored module and morphism in the indicated degree. -/
def evaluation (i : ℤ) : GradedModule A ⥤ ringedSiteModuleCategory.{u,v,w,w} J O where
  obj M := M.obj i
  map f := f.hom i
  map_id _ := rfl
  map_comp _ _ := rfl

instance evaluation_additive (i : ℤ) : (evaluation A i).Additive where
  map_add := by intros; rfl

variable {A} {M N P : GradedModule A} (f : M ⟶ N)

/-- The action on a degreewise kernel is the unique lift of the original action. -/
def kernelAction (i j : ℤ) :
    MonoidalCategory.tensorObj (kernel (f.hom i)) (A.toComplex.X j) ⟶ kernel (f.hom (i+j)) :=
  kernel.lift _ ((kernel.ι (f.hom i) ▷ A.toComplex.X j) ≫ M.smul i j) (by
    rw [Category.assoc, f.comm, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
    simp)

@[reassoc (attr := simp)] theorem kernelAction_ι (i j : ℤ) :
    kernelAction f i j ≫ kernel.ι (f.hom (i+j)) =
      (kernel.ι (f.hom i) ▷ A.toComplex.X j) ≫ M.smul i j := kernel.lift_ι _ _ _

@[reassoc] theorem kernelIndex_ι {i j : ℤ} (h : i = j) :
    eqToHom (congrArg (fun n ↦ kernel (f.hom n)) h) ≫ kernel.ι (f.hom j) =
      kernel.ι (f.hom i) ≫ eqToHom (congrArg M.obj h) := by
  subst j
  simp

/-- Associativity of the specified kernel action follows by the monic kernel inclusion. -/
theorem kernelAction_assoc (i j k : ℤ) :
    (α_ (kernel (f.hom i)) (A.toComplex.X j) (A.toComplex.X k)).hom ≫
        (kernel (f.hom i) ◁ A.mul j k) ≫ kernelAction f i (j+k) =
      (kernelAction f i j ▷ A.toComplex.X k) ≫ kernelAction f (i+j) k ≫
        eqToHom (congrArg (fun n ↦ kernel (f.hom n)) (Int.add_assoc i j k)) := by
  apply (cancel_mono (kernel.ι (f.hom (i+(j+k))))).mp
  simp only [Category.assoc]
  rw [kernelIndex_ι f (Int.add_assoc i j k)]
  simp only [kernelAction_ι_assoc, kernelAction_ι]
  rw [whisker_exchange_assoc, ← associator_naturality_left_assoc]
  rw [M.smul_assoc]
  simp only [← Category.assoc, ← comp_whiskerRight, kernelAction_ι]

/-- The unit law for the specified kernel action. -/
theorem kernelAction_unit (i : ℤ) :
    (ρ_ (kernel (f.hom i))).hom =
      (kernel (f.hom i) ◁ A.one) ≫ kernelAction f i 0 ≫
        eqToHom (congrArg (fun n ↦ kernel (f.hom n)) (add_zero i)) := by
  apply (cancel_mono (kernel.ι (f.hom i))).mp
  simp only [Category.assoc]
  rw [kernelIndex_ι f (add_zero i)]
  simp only [kernelAction_ι_assoc]
  rw [whisker_exchange_assoc, ← M.one_smul]
  exact (rightUnitor_naturality (kernel.ι (f.hom i))).symm

/-- The genuine degreewise kernel, with its induced action. -/
def kernelModule : GradedModule A where
  obj i := kernel (f.hom i)
  smul := kernelAction f
  smul_assoc := kernelAction_assoc f
  one_smul := kernelAction_unit f

def kernelInclusion : kernelModule f ⟶ M where
  hom i := kernel.ι (f.hom i)
  comm := kernelAction_ι f

theorem kernelInclusion_comp : kernelInclusion f ≫ f = 0 := by
  apply Hom.ext
  funext i
  exact kernel.condition (f.hom i)

def kernelLift (g : P ⟶ M) (h : g ≫ f = 0) : P ⟶ kernelModule f where
  hom i := kernel.lift (f.hom i) (g.hom i) (congrArg (fun k : P ⟶ N ↦ k.hom i) h)
  comm i j := by
    change P.smul i j ≫ kernel.lift (f.hom (i+j)) (g.hom (i+j)) _ =
      (kernel.lift (f.hom i) (g.hom i) _ ▷ A.toComplex.X j) ≫ kernelAction f i j
    apply (cancel_mono (kernel.ι (f.hom (i+j)))).mp
    simp only [Category.assoc, kernel.lift_ι, kernelAction_ι]
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, kernel.lift_ι]
    exact g.comm i j

theorem kernelLift_fac (g : P ⟶ M) (h : g ≫ f = 0) : kernelLift f g h ≫ kernelInclusion f = g := by
  apply Hom.ext
  funext i
  exact kernel.lift_ι _ _ _

def kernelIsLimit : IsLimit (KernelFork.ofι (kernelInclusion f) (kernelInclusion_comp f)) :=
  KernelFork.IsLimit.ofι _ _ (fun g h ↦ kernelLift f g h) (fun g h ↦ kernelLift_fac f g h)
    (fun g h k hk ↦ by
      apply Hom.ext
      funext i
      apply (cancel_mono (kernel.ι (f.hom i))).mp
      exact (congrArg (fun t : _ ⟶ M ↦ t.hom i) hk).trans (kernel.lift_ι _ _ _).symm)

theorem evaluation_preservesKernel (i : ℤ) :
    PreservesLimit (parallelPair f 0) (evaluation A i) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
  exact (isLimitMapConeForkEquiv' (evaluation A i) (kernelInclusion_comp f)).symm
    (kernelIsKernel (f.hom i))

end SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule
