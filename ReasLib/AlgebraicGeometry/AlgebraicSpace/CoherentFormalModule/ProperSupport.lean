/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion

/-!
# Coherent completion with proper support

Coherent completion restricts to the full subcategories of coherent modules
with proper support and coherent formal modules whose first stage has proper
support over the same morphism.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The object property of coherent modules with proper support over `f`. -/
def coherentProperSupportOver (f : X ⟶ Y) : ObjectProperty (Coh X) :=
  fun ℱ ↦ HasProperSupportOver f ℱ.obj

/-- Membership in `coherentProperSupportOver f` is proper support of the
underlying module. -/
theorem coherentProperSupportOver_iff (f : X ⟶ Y) (ℱ : Coh X) :
    coherentProperSupportOver f ℱ ↔ HasProperSupportOver f ℱ.obj :=
  sorry

/-- The full category of coherent modules on `X` whose support is proper over
`f`. -/
abbrev CoherentProperSupportOver (f : X ⟶ Y) :=
  (coherentProperSupportOver f).FullSubcategory

/-- A coherent module in `CoherentProperSupportOver f` has proper support over
`f`. -/
theorem coherentProperSupportOver_obj_property (f : X ⟶ Y)
    (ℱ : CoherentProperSupportOver f) :
    HasProperSupportOver f ℱ.obj.obj :=
  sorry

/-- The stage indexed by `n` of a coherent formal module. -/
abbrev coherentFormalModuleStage
    {I : IdealSubobject X} [IsQuasiCoherent I]
    (M : CoherentFormalModules X I) (n : ℕ) : Coh X :=
  M.obj.obj (op n)

/-- Stage `n` of a coherent formal module is the value of its inverse system at
`op n`. -/
theorem coherentFormalModuleStage_eq {I : IdealSubobject X} [IsQuasiCoherent I]
    (M : CoherentFormalModules X I) (n : ℕ) :
    coherentFormalModuleStage M n = M.obj.obj (op n) :=
  sorry

/-- The object property of coherent formal modules whose first stage has proper
support over `f`. -/
def coherentFormalProperSupportOver (f : X ⟶ Y) (I : IdealSubobject X)
    [IsQuasiCoherent I] : ObjectProperty (CoherentFormalModules X I) :=
  fun M ↦ HasProperSupportOver f (coherentFormalModuleStage M 1).obj

/-- Membership in `coherentFormalProperSupportOver f I` is proper support of the
first stage. -/
theorem coherentFormalProperSupportOver_iff (f : X ⟶ Y) (I : IdealSubobject X)
    [IsQuasiCoherent I] (M : CoherentFormalModules X I) :
    coherentFormalProperSupportOver f I M ↔
      HasProperSupportOver f (coherentFormalModuleStage M 1).obj :=
  sorry

/-- The full category of coherent formal modules whose first stage has proper
support over `f`. -/
abbrev CoherentFormalProperSupportOver (f : X ⟶ Y) (I : IdealSubobject X)
    [IsQuasiCoherent I] :=
  (coherentFormalProperSupportOver f I).FullSubcategory

/-- The first stage of an object of `CoherentFormalProperSupportOver f I` has
proper support over `f`. -/
theorem coherentFormalProperSupportOver_obj_property (f : X ⟶ Y)
    (I : IdealSubobject X) [IsQuasiCoherent I]
    (M : CoherentFormalProperSupportOver f I) :
    HasProperSupportOver f (coherentFormalModuleStage M.obj 1).obj :=
  sorry

/-- Canonical completion preserves proper support at the first coherent stage,
since the support of a quotient is contained in the support of the module. -/
theorem coherentCompletion_preservesProperSupportOver
    {f : X ⟶ Y} [IsNoetherian X] [LocallyOfFiniteType f]
    {I : IdealSubobject X} [IsQuasiCoherent I]
    (ℱ : CoherentProperSupportOver f) :
    HasProperSupportOver f
      (coherentFormalModuleStage
        ((CoherentCompletion.functor I).obj ℱ.obj) 1).obj :=
  sorry

/-- Canonical completion restricted from coherent modules with proper support
to coherent formal modules whose first stage has proper support. -/
noncomputable def coherentProperSupportCompletionFunctor
    (f : X ⟶ Y) (I : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f] [IsQuasiCoherent I] :
    CoherentProperSupportOver f ⥤ CoherentFormalProperSupportOver f I :=
  (coherentFormalProperSupportOver f I).lift
    ((coherentProperSupportOver f).ι ⋙ CoherentCompletion.functor I)
    coherentCompletion_preservesProperSupportOver

/-- The restricted completion functor agrees on underlying inverse systems with
unrestricted coherent completion. -/
theorem coherentProperSupportCompletionFunctor_obj
    (f : X ⟶ Y) (I : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f] [IsQuasiCoherent I]
    (ℱ : CoherentProperSupportOver f) :
    ((coherentProperSupportCompletionFunctor f I).obj ℱ).obj =
      (CoherentCompletion.functor I).obj ℱ.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
