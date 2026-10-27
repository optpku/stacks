/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.TensorUnit

/-! # Symmetric monoidal coherent modules

Coherent modules on a locally Noetherian algebraic stack inherit the ambient
fppf tensor product and its symmetric monoidal structure.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Coh

variable {S : Scheme.{u}}

/-- The coherent structure module on the fppf ringed site of a locally
Noetherian algebraic stack. -/
def structureSheaf (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] : Coh X where
  obj := SheafOfModules.unit (GroupoidsOver.structureSheaf X)
  property := instIsCoherentUnit X

/-- The underlying module of the coherent structure sheaf is the structure module. -/
theorem structureSheaf_obj (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    (structureSheaf X).obj = SheafOfModules.unit (GroupoidsOver.structureSheaf X) :=
  rfl

/-- Inclusion into quasi-coherent modules identifies the two structure modules. -/
def structureSheaf_toQCohIso (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    toQCoh.obj (structureSheaf X) ≅ QCoh.structureSheaf X :=
  isoMk (quasiCoherentModuleProperty X) (Iso.refl _)

/-- The ambient fppf tensor unit is coherent on a locally Noetherian algebraic stack. -/
theorem unit_mem (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] :
    coherentModuleProperty X
      (𝟙_ (RingedSite.ModuleCat.{u} (ringedSite X))) :=
  sorry

/-- Coherent modules are closed under the ambient fppf tensor product and contain its unit. -/
instance isMonoidal (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] : (coherentModuleProperty X).IsMonoidal where
  prop_unit := unit_mem X
  prop_tensor F G hF hG := tensor_isCoherent ⟨F, hF⟩ ⟨G, hG⟩

/-- The inherited tensor product agrees definitionally with the coherent tensor construction. -/
theorem tensorObj_eq {X : GroupoidsOver S} [AlgebraicStack X]
    [IsLocallyNoetherian X] (A B : Coh X) :
    (A ⊗ B : Coh X) = tensor A B :=
  rfl

/-- The coherent structure module is canonically isomorphic to the tensor unit. -/
def structureSheafIsoTensorUnit (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] : structureSheaf X ≅ 𝟙_ (Coh X) :=
  isoMk (coherentModuleProperty X)
    ((quasiCoherentModuleProperty X).ι.mapIso (QCoh.structureSheafIsoTensorUnit X))

end AlgebraicGeometry.AlgebraicStack.Coh
