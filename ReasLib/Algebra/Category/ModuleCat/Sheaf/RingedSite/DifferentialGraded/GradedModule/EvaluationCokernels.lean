module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule.EvaluationKernels
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.ColimitWitness

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
noncomputable section
universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}} {A : DGA(O)}
variable {M N P : GradedModule A} (f : M ⟶ N)

/-- The right-exact tensor functor takes the actual degreewise cokernel to a cokernel. -/
def tensorCokernelIsColimit (i j : ℤ) :
    IsColimit (CokernelCofork.ofπ (cokernel.π (f.hom i) ▷ A.toComplex.X j)
      (by rw [← MonoidalCategory.comp_whiskerRight, cokernel.condition]; simp) :
        CokernelCofork (f.hom i ▷ A.toComplex.X j)) :=
  isColimitMapCoconeCoforkEquiv' (tensorRight (A.toComplex.X j))
    (cokernel.condition (f.hom i))
    (Tensor.rightMapColimit (cokernelIsCokernel (f.hom i)) (A.toComplex.X j))

theorem cokernelAction_condition (i j : ℤ) :
    (f.hom i ▷ A.toComplex.X j) ≫ N.smul i j ≫ cokernel.π (f.hom (i+j)) = 0 := by
  rw [← Category.assoc, ← f.comm, Category.assoc, cokernel.condition, comp_zero]

/-- The quotient action descends the original action through the actual tensor cokernel. -/
def cokernelAction (i j : ℤ) :
    MonoidalCategory.tensorObj (cokernel (f.hom i)) (A.toComplex.X j) ⟶ cokernel (f.hom (i+j)) :=
  (tensorCokernelIsColimit f i j).desc
    (CokernelCofork.ofπ (N.smul i j ≫ cokernel.π (f.hom (i+j))) (cokernelAction_condition f i j))

@[reassoc (attr := simp)] theorem π_cokernelAction (i j : ℤ) :
    (cokernel.π (f.hom i) ▷ A.toComplex.X j) ≫ cokernelAction f i j =
      N.smul i j ≫ cokernel.π (f.hom (i+j)) :=
  (tensorCokernelIsColimit f i j).fac _ WalkingParallelPair.one

@[reassoc] theorem π_cokernelIndex {i j : ℤ} (h : i = j) :
    cokernel.π (f.hom i) ≫ eqToHom (congrArg (fun n ↦ cokernel (f.hom n)) h) =
      eqToHom (congrArg N.obj h) ≫ cokernel.π (f.hom j) := by
  subst j
  simp

/-- Associativity of the specified quotient action follows by the epic quotient projections. -/
theorem cokernelAction_assoc (i j k : ℤ) :
    (α_ (cokernel (f.hom i)) (A.toComplex.X j) (A.toComplex.X k)).hom ≫
        (cokernel (f.hom i) ◁ A.mul j k) ≫ cokernelAction f i (j+k) =
      (cokernelAction f i j ▷ A.toComplex.X k) ≫ cokernelAction f (i+j) k ≫
        eqToHom (congrArg (fun n ↦ cokernel (f.hom n)) (Int.add_assoc i j k)) := by
  letI := Tensor.rightPreservesFiniteColimits (A.toComplex.X j)
  letI := Tensor.rightPreservesFiniteColimits (A.toComplex.X k)
  haveI : Epi (cokernel.π (f.hom i) ▷ A.toComplex.X j) :=
    (tensorRight (A.toComplex.X j)).map_epi _
  haveI : Epi ((cokernel.π (f.hom i) ▷ A.toComplex.X j) ▷ A.toComplex.X k) :=
    (tensorRight (A.toComplex.X k)).map_epi _
  apply (cancel_epi ((cokernel.π (f.hom i) ▷ A.toComplex.X j) ▷ A.toComplex.X k)).mp
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, π_cokernelAction]
  rw [← comp_whiskerRight_assoc, π_cokernelAction]
  simp only [comp_whiskerRight, Category.assoc, π_cokernelAction_assoc]
  rw [π_cokernelIndex f (Int.add_assoc i j k)]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ cokernel.π (f.hom (i+(j+k)))) (N.smul_assoc i j k)

theorem cokernelAction_unit (i : ℤ) :
    (ρ_ (cokernel (f.hom i))).hom =
      (cokernel (f.hom i) ◁ A.one) ≫ cokernelAction f i 0 ≫
        eqToHom (congrArg (fun n ↦ cokernel (f.hom n)) (add_zero i)) := by
  letI := Tensor.rightPreservesFiniteColimits (𝟙_ (ringedSiteModuleCategory.{u,v,w,w} J O))
  haveI : Epi (cokernel.π (f.hom i) ▷ (𝟙_ (ringedSiteModuleCategory.{u,v,w,w} J O))) :=
    (tensorRight _).map_epi _
  apply (cancel_epi (cokernel.π (f.hom i) ▷ (𝟙_ (ringedSiteModuleCategory.{u,v,w,w} J O)))).mp
  rw [rightUnitor_naturality]
  rw [← whisker_exchange_assoc, π_cokernelAction_assoc, π_cokernelIndex f (add_zero i)]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ cokernel.π (f.hom i)) (N.one_smul i)

def cokernelModule : GradedModule A where
  obj i := cokernel (f.hom i)
  smul := cokernelAction f
  smul_assoc := cokernelAction_assoc f
  one_smul := cokernelAction_unit f

def cokernelProjection : N ⟶ cokernelModule f where
  hom i := cokernel.π (f.hom i)
  comm i j := (π_cokernelAction f i j).symm

theorem comp_cokernelProjection : f ≫ cokernelProjection f = 0 := by
  apply Hom.ext
  funext i
  exact cokernel.condition (f.hom i)

def cokernelDesc (g : N ⟶ P) (h : f ≫ g = 0) : cokernelModule f ⟶ P where
  hom i := cokernel.desc (f.hom i) (g.hom i) (congrArg (fun k : M ⟶ P ↦ k.hom i) h)
  comm i j := by
    letI := Tensor.rightPreservesFiniteColimits (A.toComplex.X j)
    change cokernelAction f i j ≫ cokernel.desc (f.hom (i+j)) (g.hom (i+j)) _ =
      (cokernel.desc (f.hom i) (g.hom i) _ ▷ A.toComplex.X j) ≫ P.smul i j
    haveI : Epi (cokernel.π (f.hom i) ▷ A.toComplex.X j) :=
      (tensorRight (A.toComplex.X j)).map_epi _
    apply (cancel_epi (cokernel.π (f.hom i) ▷ A.toComplex.X j)).mp
    rw [← Category.assoc, π_cokernelAction, Category.assoc, cokernel.π_desc]
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, cokernel.π_desc]
    exact g.comm i j

theorem cokernelDesc_fac (g : N ⟶ P) (h : f ≫ g = 0) :
    cokernelProjection f ≫ cokernelDesc f g h = g := by
  apply Hom.ext
  funext i
  exact cokernel.π_desc _ _ _

def cokernelIsColimit : IsColimit (CokernelCofork.ofπ (cokernelProjection f) (comp_cokernelProjection f)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun g h ↦ cokernelDesc f g h) (fun g h ↦ cokernelDesc_fac f g h)
    (fun g h k hk ↦ by
      apply Hom.ext
      funext i
      apply (cancel_epi (cokernel.π (f.hom i))).mp
      exact (congrArg (fun t : N ⟶ _ ↦ t.hom i) hk).trans (cokernel.π_desc _ _ _).symm)

theorem evaluation_preservesCokernel (i : ℤ) :
    PreservesColimit (parallelPair f 0) (evaluation A i) := by
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
  exact (isColimitMapCoconeCoforkEquiv' (evaluation A i) (comp_cokernelProjection f)).symm
    (cokernelIsCokernel (f.hom i))

end SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule
