/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.ResolutionConstruction
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective

/-!
# The specified property-P replacement and its homotopy descent

The strict all-labels replacement is deliberately not asserted additive: its value on a zero
map need not be zero. Naturality of its actual quasi-isomorphic augmentation and K-projectivity
of its source give representative independence and linearity after passing to homotopy classes.
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.PropertyP
variable {R : Type u} [CommRing R] (A : CochainDGAlgebra.{u, v} R)

namespace Resolution
/-- The actual reviewed all-pairs constructor, exposed by the existing resolution owner. -/
def canonical (M : DifferentialGradedModule.{u, v} A) : Resolution A M :=
  PrivateConstruction.resolution M

@[simp] theorem canonical_obj (M : DifferentialGradedModule.{u, v} A) :
    (canonical A M).obj = PrivateConstruction.omegaObj M := rfl
@[simp] theorem canonical_π (M : DifferentialGradedModule.{u, v} A) :
    (canonical A M).π = PrivateConstruction.omegaπ M := rfl
@[simp] theorem canonical_filtration (M : DifferentialGradedModule.{u, v} A) :
    (canonical A M).filtration = PrivateConstruction.omegaFiltration M := rfl
end Resolution

/-- The strict replacement retains the actual quotient maps; it is an ordinary functor. -/
abbrev replacementFunctor : DifferentialGradedModule.{u, v} A ⥤ DifferentialGradedModule.{u, v} A :=
  PrivateConstruction.omegaFunctor A

/-- The specified augmentation on strict modules. -/
abbrev replacementAugmentation : replacementFunctor A ⟶ 𝟭 (DifferentialGradedModule.{u, v} A) :=
  PrivateConstruction.omegaAugmentation A

/-- Homotopic closed maps induce the same replacement map in the homotopy category.
Postcomposition with the target augmentation detects this equality out of the property-P source.
This does not claim that replacement preserves a specified strict homotopy. -/
theorem replacement_homotopy_sound {M N : DifferentialGradedModule.{u, v} A}
    (f g : CompHom M N) (h : DifferentialGradedCategory.Homotopic M N f g) :
    (toK A).map ((replacementFunctor A).map (compHomToHom f)) =
      (toK A).map ((replacementFunctor A).map (compHomToHom g)) := sorry

/-- Replace a homotopy class using the actual strict map on any closed representative. -/
def homotopyReplacement :
    DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A) ⥤
      DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A) where
  obj X := ⟨(Resolution.canonical A X.obj).obj⟩
  map {X Y} f := _root_.Quotient.lift
    (fun a : CompHom X.obj Y.obj ↦
      (toK A).map ((replacementFunctor A).map (compHomToHom a)))
    (fun a b h ↦ replacement_homotopy_sound A a b h) f
  map_id := sorry
  map_comp := sorry

/-- The homotopy-level augmentation has the actual strict augmentation components. -/
def homotopyAugmentation : homotopyReplacement A ⟶
    𝟭 (DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) where
  app X := (toK A).map (Resolution.canonical A X.obj).π
  naturality := sorry

/-- The image object retains its supplied property-P filtration. -/
theorem homotopyReplacement_propertyP
    (X : DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) :
    HasPropertyP A ((homotopyReplacement A).obj X).obj :=
  ⟨(Resolution.canonical A X.obj).filtration⟩

/-- The nonadditive strict relabelling becomes additive on homotopy classes. -/
instance homotopyReplacement_additive : (homotopyReplacement A).Additive := sorry
instance homotopyReplacement_linear : (homotopyReplacement A).Linear R := sorry

/-- Two-out-of-three with the actual augmentation gives the weak-equivalence law. -/
theorem homotopyReplacement_mem_trW
    {X Y : DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)}
    (f : X ⟶ Y) (hf : (Homotopy.acyclic A).trW f) :
    (Homotopy.acyclic A).trW ((homotopyReplacement A).map f) := sorry

@[simp] theorem homotopyAugmentation_app
    (X : DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) :
    (homotopyAugmentation A).app X = (toK A).map (PrivateConstruction.omegaπ X.obj) := rfl

end DifferentialGradedModule.PropertyP
