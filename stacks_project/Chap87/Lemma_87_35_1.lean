/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.StructureSheaf.Existence

/-!
# Existence of the structure sheaf of a formal algebraic space

Every formal algebraic space admits a sheaf of topological rings on its small
étale site whose underlying sheaf of rings is a structure sheaf: on each affine
étale object `U_red`, the value is the inverse-limit ring of stage global
sections of any directed affine thickening presentation of `U`.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace (AffineEtaleOver)
open AlgebraicGeometry.FormalAlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 87.35.1: every formal algebraic space has a structure sheaf. -/
@[stacks 0DEJ] #check (AlgebraicGeometry.FormalAlgebraicSpace.exists_structureSheaf :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X],
    ∃ 𝒪 : Sheaf (AlgebraicSpace.smallEtaleTopology (reduction X)) TopCommRingCat.{u},
      IsStructureSheaf (topCommRingSheafToRingSheaf 𝒪) ∧
        ∀ (U : AffineEtaleOver X) {Λ : Type u} [Preorder Λ]
          [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
          [IsDirectedAffineThickeningColimit D U.obj.left]
          (w : ColimitPresentation D U.obj.left),
          Nonempty (structureSheafTopSections 𝒪 U ≅ stageLimitTopRing D))

/- The topological and underlying-ring identifications can be chosen compatibly
and naturally in morphisms of affine thickening presentations. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.exists_structureSheaf_spec :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [R : Reduction X],
    ∃ (𝒪 : Sheaf (AlgebraicSpace.smallEtaleTopology (reduction X)) TopCommRingCat.{u})
      (η :
        ∀ (U : AffineEtaleOver X) {Λ : Type u} [Preorder Λ]
          [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
          [IsDirectedAffineThickeningColimit D U.obj.left],
          ColimitPresentation D U.obj.left →
            (structureSheafTopSections 𝒪 U ≅ stageLimitTopRing D))
      (ρ :
        ∀ (U : AffineEtaleOver X) {Λ : Type u} [Preorder Λ]
          [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
          [IsDirectedAffineThickeningColimit D U.obj.left],
          ColimitPresentation D U.obj.left →
            (structureSheafSections (topCommRingSheafToRingSheaf 𝒪) U ≅
              stageLimitRing D)),
      IsStructureSheaf (topCommRingSheafToRingSheaf 𝒪) ∧
        ((∀ (U : AffineEtaleOver X) {Λ : Type u} [Preorder Λ]
            [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
            [IsDirectedAffineThickeningColimit D U.obj.left]
            (w : ColimitPresentation D U.obj.left),
          (forget₂ TopCommRingCat CommRingCat ⋙
              forget₂ CommRingCat RingCat).mapIso (η U D w) =
            eqToIso (forget_structureSheafTopSections 𝒪 U) ≪≫
              ρ U D w ≪≫
                eqToIso (stageLimitTopRing_forgetToRing D).symm) ∧
          ∀ {U V : AffineEtaleOver X} (f : U ⟶ V) {Λ Λ' : Type u}
            [Preorder Λ] [Preorder Λ'] [IsDirected Λ (· ≤ ·)]
            [IsDirected Λ' (· ≤ ·)] (D : Λ ⥤ Over S) (D' : Λ' ⥤ Over S)
            [IsDirectedAffineThickeningColimit D U.obj.left]
            [IsDirectedAffineThickeningColimit D' V.obj.left]
            (wU : ColimitPresentation D U.obj.left)
            (wV : ColimitPresentation D' V.obj.left)
            (F : Λ ⥤ Λ') (τ : D ⟶ F ⋙ D'),
            IsCompatiblePresentation wU wV f.hom.left F τ →
              (topCommRingSheafToRingSheaf 𝒪).obj.map
                  ((AlgebraicSpace.affineEtaleInclusion (reduction X)).map
                    ((ReductionData.toAffineEtale R.toReductionData).map f)).op ≫
                (ρ U D wU).hom =
                (ρ V D' wV).hom ≫ stageLimitRing.map F τ))
