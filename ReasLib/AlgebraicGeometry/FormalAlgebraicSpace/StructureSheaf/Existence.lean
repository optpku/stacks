/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.StructureSheaf.Topological

/-! # Existence of topological structure sheaves on formal algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace (AffineEtaleOver)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- Every formal algebraic space has a sheaf of topological commutative rings
whose underlying ring sheaf is a structure sheaf and whose affine étale values
are the inverse limits of discrete stage global-section rings. -/
theorem exists_structureSheaf (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X] :
    ∃ 𝒪 : Sheaf (AlgebraicSpace.smallEtaleTopology (reduction X)) TopCommRingCat.{u},
      IsStructureSheaf (topCommRingSheafToRingSheaf 𝒪) ∧
        ∀ (U : AffineEtaleOver X) {Λ : Type u} [Preorder Λ]
          [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
          [IsDirectedAffineThickeningColimit D U.obj.left]
          (w : ColimitPresentation D U.obj.left),
          Nonempty (structureSheafTopSections 𝒪 U ≅ stageLimitTopRing D) := sorry

/-- A structure sheaf of topological rings may be chosen so that the
inverse-limit identifications are isomorphisms of topological rings whose
images under `forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat`
are the ring isomorphisms of `IsStructureSheaf`, naturally in compatible
presentations. -/
theorem exists_structureSheaf_spec {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [R : Reduction X] :
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
                (ρ V D' wV).hom ≫ stageLimitRing.map F τ) := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
