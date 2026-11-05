/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# Tensor closure of coherent scheme modules

Tensor products of coherent modules on a locally Noetherian scheme are coherent.
Tensoring a coherent module with a finite locally free module needs no Noetherian hypothesis.
The corresponding internal-Hom closure theorem is reexported for compatibility.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {X : Scheme.{u}}
variable {F G : X.Modules}

/-- The tensor unit of scheme modules is coherent on a locally Noetherian scheme. -/
theorem tensorUnit_isCoherent_of_isLocallyNoetherian [IsLocallyNoetherian X] :
    (𝟙_ X.Modules).IsCoherent := sorry

/-- The tensor unit of scheme modules is canonically coherent on a locally Noetherian scheme. -/
instance instIsCoherentTensorUnit [IsLocallyNoetherian X] : (𝟙_ X.Modules).IsCoherent :=
  tensorUnit_isCoherent_of_isLocallyNoetherian

/-- The tensor product of coherent modules on a locally Noetherian scheme is coherent. -/
@[stacks 01Y2, instance]
theorem isCoherent_tensor
    [IsLocallyNoetherian X] [F.IsCoherent] [G.IsCoherent] :
    (F ⊗ G).IsCoherent := sorry

end

/-- On any scheme, tensoring a coherent module with a finite locally free module preserves
coherence. The local ranks may vary, and the structure sheaf need not be coherent.

This specializes coherence under tensoring with a finitely presented sheaf. Locally, a finite
free right factor of rank `r` gives a direct sum of `r` copies of the left factor: rank zero
gives the zero module, rank one gives the left factor, and every finite rank preserves
coherence by finite direct-sum closure. -/
theorem isCoherent_tensor_of_isFiniteLocallyFree
    {X : Scheme.{u}} (F G : X.Modules) [hF : F.IsCoherent] [IsFiniteLocallyFree G] :
    (F ⊗ G).IsCoherent := by
  exact @SheafOfModules.IsCoherent.tensor_of_finitePresentation_right
    _ _ _ _ _ _ X.𝒪 _ _ _ _ F G hF
      (SheafOfModules.IsFiniteLocallyFree.isFinitePresentation G)

/-- Tensoring a coherent scheme module with an invertible module preserves coherence,
without a Noetherian hypothesis. The rank-one bridge is installed only in this proof. -/
theorem isCoherent_tensor_of_isInvertible
    {X : Scheme.{u}} (F G : X.Modules) [F.IsCoherent] [Invertible G] :
    (F ⊗ G).IsCoherent := by
  letI : IsFiniteLocallyFreeOfRank 1 G := isFiniteLocallyFreeOfRankOne_of_invertible G
  exact isCoherent_tensor_of_isFiniteLocallyFree F G

/-- On a scheme proper over a field, tensoring a coherent module with a finite locally free
module of constant rank produces a coherent module. -/
theorem isCoherent_tensor_of_isProper_over_field
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent]
    (n : ℕ) (G : X.Modules) [IsFiniteLocallyFreeOfRank n G] :
    (F ⊗ G : X.Modules).IsCoherent :=
  isCoherent_tensor_of_isFiniteLocallyFree F G

/-- Tensoring with an invertible module preserves injectivity of multiplication by a section. -/
theorem smul_injective_tensor {X : Scheme.{u}} (F G : X.Modules) [Invertible G]
    (V : X.Opens) (s : Γ(X, V)) (hF : Function.Injective (F.smul s).hom) :
    Function.Injective ((F ⊗ G).smul s).hom := sorry

end AlgebraicGeometry.Scheme.Modules
