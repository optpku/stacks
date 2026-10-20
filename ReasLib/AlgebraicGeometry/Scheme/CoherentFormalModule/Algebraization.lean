/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.MapAnnihilation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.IdealPower

/-!
# Algebraization of maps of coherent formal modules

This file records algebraization data and uniqueness for maps between coherent formal modules
and completions of coherent modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {X : Scheme.{u}}

/-- A morphism of scheme modules has kernel and cokernel uniformly annihilated on affine opens
by powers of an ideal sheaf. -/
def HasIdealPowerTorsionKernelCokernel
    (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) : Prop :=
  IsAnnihilatedByIdealPowerOnAffineOpens I (kernel f) ∧
    IsAnnihilatedByIdealPowerOnAffineOpens I (cokernel f)

/-- Kernel-and-cokernel ideal-power torsion is the conjunction of the corresponding
annihilation conditions. -/
theorem hasIdealPowerTorsionKernelCokernel_iff
    (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) :
    HasIdealPowerTorsionKernelCokernel I f ↔
      IsAnnihilatedByIdealPowerOnAffineOpens I (kernel f) ∧
        IsAnnihilatedByIdealPowerOnAffineOpens I (cokernel f) :=
  Iff.rfl

end Modules

/-- Algebraization data for a morphism from a coherent formal module to the completion of a
coherent module. -/
structure FormalMapToCompletionAlgebraization
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (E : CoherentFormalModules X I) (G : RingedSpace.Coh X.toRingedSpace)
    (alpha : E ⟶ ctx.obj G) where
  /-- The coherent module underlying the algebraization. -/
  F : RingedSpace.Coh X.toRingedSpace
  /-- The morphism from the algebraized coherent module to the target coherent module. -/
  a : F ⟶ G
  /-- The underlying module morphism has ideal-power-torsion kernel and cokernel. -/
  torsion : Modules.HasIdealPowerTorsionKernelCokernel I
    ((SheafOfModules.isCoherent X.ringCatSheaf).ι.map a)
  /-- The given formal module is isomorphic to the completion of the algebraized module. -/
  beta : E ≅ ctx.obj F
  /-- The formal morphism is induced by the algebraized morphism through the isomorphism. -/
  comm : alpha = beta.hom ≫ ctx.map a

/-- An isomorphism between algebraizations of a map to a completion is compatible when it
intertwines their algebraized maps and completion isomorphisms. -/
def FormalMapToCompletionAlgebraization.IsomorphismCompatible
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {ctx : CoherentCompletionFunctor X I}
    {E : CoherentFormalModules X I} {G : RingedSpace.Coh X.toRingedSpace}
    {alpha : E ⟶ ctx.obj G}
    (z z' : FormalMapToCompletionAlgebraization ctx E G alpha) (e : z.F ≅ z'.F) : Prop :=
  e.hom ≫ z'.a = z.a ∧
    z.beta.hom ≫ ctx.map e.hom = z'.beta.hom

/-- Compatibility of an isomorphism between algebraizations of a map to a completion unfolds
to its two intertwining equations. -/
theorem FormalMapToCompletionAlgebraization.isomorphismCompatible_iff
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {ctx : CoherentCompletionFunctor X I}
    {E : CoherentFormalModules X I} {G : RingedSpace.Coh X.toRingedSpace}
    {alpha : E ⟶ ctx.obj G}
    (z z' : FormalMapToCompletionAlgebraization ctx E G alpha) (e : z.F ≅ z'.F) :
    FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e ↔
      e.hom ≫ z'.a = z.a ∧
        z.beta.hom ≫ ctx.map e.hom = z'.beta.hom :=
  Iff.rfl

/-- Algebraization data for a morphism from the completion of a coherent module to a coherent
formal module. -/
structure CompletionToFormalMapAlgebraization
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (G : RingedSpace.Coh X.toRingedSpace) (E : CoherentFormalModules X I)
    (alpha : ctx.obj G ⟶ E) where
  /-- The coherent module underlying the algebraization. -/
  F : RingedSpace.Coh X.toRingedSpace
  /-- The morphism from the source coherent module to the algebraized coherent module. -/
  a : G ⟶ F
  /-- The underlying module morphism has ideal-power-torsion kernel and cokernel. -/
  torsion : Modules.HasIdealPowerTorsionKernelCokernel I
    ((SheafOfModules.isCoherent X.ringCatSheaf).ι.map a)
  /-- The completion of the algebraized module is isomorphic to the given formal module. -/
  beta : ctx.obj F ≅ E
  /-- The formal morphism is induced by the algebraized morphism through the isomorphism. -/
  comm : alpha = ctx.map a ≫ beta.hom

/-- An isomorphism between algebraizations of a map from a completion is compatible when it
intertwines their algebraized maps and completion isomorphisms. -/
def CompletionToFormalMapAlgebraization.IsomorphismCompatible
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {ctx : CoherentCompletionFunctor X I}
    {G : RingedSpace.Coh X.toRingedSpace} {E : CoherentFormalModules X I}
    {alpha : ctx.obj G ⟶ E}
    (z z' : CompletionToFormalMapAlgebraization ctx G E alpha) (e : z.F ≅ z'.F) : Prop :=
  z.a ≫ e.hom = z'.a ∧
    ctx.map e.hom ≫ z'.beta.hom = z.beta.hom

/-- Compatibility of an isomorphism between algebraizations of a map from a completion unfolds
to its two intertwining equations. -/
theorem CompletionToFormalMapAlgebraization.isomorphismCompatible_iff
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {ctx : CoherentCompletionFunctor X I}
    {G : RingedSpace.Coh X.toRingedSpace} {E : CoherentFormalModules X I}
    {alpha : ctx.obj G ⟶ E}
    (z z' : CompletionToFormalMapAlgebraization ctx G E alpha) (e : z.F ≅ z'.F) :
    CompletionToFormalMapAlgebraization.IsomorphismCompatible z z' e ↔
      z.a ≫ e.hom = z'.a ∧
        ctx.map e.hom ≫ z'.beta.hom = z.beta.hom :=
  Iff.rfl

/-- A coherent-formal morphism to the completion of a coherent module whose stagewise kernels
and cokernels are uniformly annihilated by an ideal power has an algebraization, unique up to a
unique compatible isomorphism. -/
theorem existsUnique_algebraization_of_formalMap_to_completion
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (E : CoherentFormalModules X I) (G : RingedSpace.Coh X.toRingedSpace)
    (alpha : E ⟶ ctx.obj G)
    (halpha : CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I alpha) :
    ∃ z : FormalMapToCompletionAlgebraization ctx E G alpha,
      ∀ z' : FormalMapToCompletionAlgebraization ctx E G alpha,
        ∃! e : z.F ≅ z'.F,
          FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e := sorry

/-- A coherent-formal morphism from the completion of a coherent module whose stagewise kernels
and cokernels are uniformly annihilated by an ideal power has an algebraization, unique up to a
unique compatible isomorphism. -/
theorem existsUnique_algebraization_of_completion_to_formalMap
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (G : RingedSpace.Coh X.toRingedSpace) (E : CoherentFormalModules X I)
    (alpha : ctx.obj G ⟶ E)
    (halpha : CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I alpha) :
    ∃ z : CompletionToFormalMapAlgebraization ctx G E alpha,
      ∀ z' : CompletionToFormalMapAlgebraization ctx G E alpha,
        ∃! e : z.F ≅ z'.F,
          CompletionToFormalMapAlgebraization.IsomorphismCompatible z z' e := sorry

namespace CoherentCompletion

/-- Lemma 30.23.6 (0889) (1): a map to a canonical completion with uniformly ideal-power
annihilated stagewise kernel and cokernel has a unique algebraization. -/
@[stacks 0889 "algebraization of a map to canonical completion"]
theorem existsUnique_algebraization_to
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (E : CoherentFormalModules X I) (G : RingedSpace.Coh X.toRingedSpace)
    (alpha : E ⟶ (functor I).obj G)
    (halpha : CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I alpha) :
    ∃ z : FormalMapToCompletionAlgebraization
        (CoherentCompletionFunctor.canonical X I) E G alpha,
      ∀ z' : FormalMapToCompletionAlgebraization
          (CoherentCompletionFunctor.canonical X I) E G alpha,
        ∃! e : z.F ≅ z'.F,
          FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e := sorry

/-- Lemma 30.23.6 (0889) (2): a map from a canonical completion with uniformly ideal-power
annihilated stagewise kernel and cokernel has a unique algebraization. -/
@[stacks 0889 "algebraization of a map from canonical completion"]
theorem existsUnique_algebraization_from
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (G : RingedSpace.Coh X.toRingedSpace) (E : CoherentFormalModules X I)
    (alpha : (functor I).obj G ⟶ E)
    (halpha : CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I alpha) :
    ∃ z : CompletionToFormalMapAlgebraization
        (CoherentCompletionFunctor.canonical X I) G E alpha,
      ∀ z' : CompletionToFormalMapAlgebraization
          (CoherentCompletionFunctor.canonical X I) G E alpha,
        ∃! e : z.F ≅ z'.F,
          CompletionToFormalMapAlgebraization.IsomorphismCompatible z z' e := sorry

end CoherentCompletion

end AlgebraicGeometry.Scheme
