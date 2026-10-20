/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Types
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale

/-!
# Affine algebraization of rig-étale morphisms into completions

Rig-étale morphisms into completions of Noetherian affine algebraic spaces
admit compatible affine algebraizations of finite type, étale off the closed
subset. Such an algebraization is étale when the formal morphism is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- A rig-étale morphism from a Noetherian affine formal algebraic space into
the completion of a Noetherian affine algebraic space along a closed subset
admits an affine finite-type algebraization, étale over the open complement,
with a compatible isomorphism of its completion with the given formal space. -/
theorem exists_affineAlgebraize {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAffine X] [IsNoetherian X] (T : Closeds (Points X))
    {W : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
    [FormalAlgebraicSpace.IsAffine W] [FormalAlgebraicSpace.IsNoetherianAffine W]
    (g : W ⟶ completionAlong X T) [FormalAlgebraicSpace.RigEtale g] :
    ∃ (X' : AlgebraicSpace S) (_ : IsAffine X') (f : X' ⟶ X) (_ : FiniteType f)
      (_ : Etale (openInverseImageTo f (openComplementι X T)))
      (e : completionAlong X' (T.preimage (Points.continuous_map f)) ≅ W),
      e.hom ≫ g = map f T :=
  sorry

/-- A finite-type morphism of affine algebraic spaces with Noetherian target
is étale if it is étale over the complement of a closed subset and its induced
completion morphism is identified with an étale morphism from a Noetherian
affine formal algebraic space. -/
theorem etale_of_etale {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsAffine X] [IsNoetherian X] [IsAffine X'] (T : Closeds (Points X))
    (f : X' ⟶ X) [FiniteType f]
    (hf : Etale (openInverseImageTo f (openComplementι X T)))
    {W : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
    [FormalAlgebraicSpace.IsAffine W] [FormalAlgebraicSpace.IsNoetherianAffine W]
    (g : W ⟶ completionAlong X T) [FormalAlgebraicSpace.RigEtale g]
    [FormalAlgebraicSpace.Etale g]
    (e : completionAlong X' (T.preimage (Points.continuous_map f)) ≅ W)
    (he : e.hom ≫ g = map f T) : Etale f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.completionAlong
