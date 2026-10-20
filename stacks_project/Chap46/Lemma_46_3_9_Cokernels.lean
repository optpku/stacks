module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import stacks_project.Chap46.Definition_46_3_2_Instances

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- The objectwise cokernel of a morphism of module-valued functors. -/
def cokernelObj {F G : ModuleValuedFunctor.{u, v} A} (f : F ⟶ G) :
    ModuleValuedFunctor.{u, v} A where
  obj B := cokernel (f.app B)
  map {B B'} g :=
    cokernel.desc (f.app B)
      (G.map g ≫ (ModuleCat.restrictScalars g.right.hom).map (cokernel.π (f.app B'))) sorry
  map_id := sorry
  map_comp := sorry

/-- The canonical projection to the objectwise cokernel of a morphism of
module-valued functors. -/
def cokernelπ {F G : ModuleValuedFunctor.{u, v} A} (f : F ⟶ G) :
    G ⟶ cokernelObj f where
  app B := cokernel.π (f.app B)
  naturality := sorry

/-- The objectwise cokernel projection annihilates the original morphism. -/
theorem comp_cokernelπ {F G : ModuleValuedFunctor.{u, v} A} (f : F ⟶ G) :
    f ≫ cokernelπ f = 0 := sorry

/-- The morphism from an objectwise cokernel induced by a morphism annihilating the
original map. -/
def cokernelDesc {F G H : ModuleValuedFunctor.{u, v} A} (f : F ⟶ G)
    (g : G ⟶ H) (h : f ≫ g = 0) : cokernelObj f ⟶ H where
  app B := cokernel.desc (f.app B) (g.app B) sorry
  naturality := sorry

/-- The canonical objectwise cokernel cofork of a morphism of module-valued functors. -/
def cokernelCofork {F G : ModuleValuedFunctor.{u, v} A} (f : F ⟶ G) :
    CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)

/-- The objectwise cokernel cofork satisfies the categorical universal property. -/
def cokernelCoforkIsColimit {F G : ModuleValuedFunctor.{u, v} A} (f : F ⟶ G) :
    IsColimit (cokernelCofork f) where
  desc s := cokernelDesc f (Cofork.π s) (CokernelCofork.condition s)
  fac := sorry
  uniq := sorry

/-- Module-valued functors admit cokernels computed objectwise. -/
noncomputable instance instHasCokernels : HasCokernels (ModuleValuedFunctor.{u, v} A) where
  has_colimit f := HasColimit.mk ⟨cokernelCofork f, cokernelCoforkIsColimit f⟩

end ModuleValuedFunctor
