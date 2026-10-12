/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_35_1_Topological

/-!
# Existence of the structure sheaf of a formal algebraic space

Every formal algebraic space admits a sheaf of topological rings on its small
étale site whose underlying sheaf of rings is a structure sheaf: on each affine
étale object `U_red`, the value is the inverse-limit ring of stage global
sections of any directed affine thickening presentation of `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace (AffineEtaleOver)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- Lemma 87.35.1: every formal algebraic space has a structure sheaf. -/
@[stacks 0DEJ]
theorem exists_structureSheaf (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] :
    ∃ 𝒪 : Sheaf (smallEtaleTopology X) TopCommRingCat.{u},
      IsStructureSheaf (topCommRingSheafToRingSheaf 𝒪) ∧
        ∀ (U : AffineEtaleOver X) {Λ : Type u} [Preorder Λ]
          [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
          [IsDirectedAffineThickeningColimit D U.obj.left]
          (w : ColimitPresentation D U.obj.left),
          Nonempty (structureSheafTopSections 𝒪 U ≅ stageLimitTopRing D) :=
  sorry

/-- A structure sheaf of topological rings may be chosen so that the
inverse-limit identifications are isomorphisms of topological rings whose
images under `forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat`
are the ring isomorphisms of `IsStructureSheaf`, naturally in compatible
presentations. -/
theorem exists_structureSheaf_spec {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] :
    ∃ (𝒪 : Sheaf (smallEtaleTopology X) TopCommRingCat.{u})
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
                eqToIso (stageLimitTopRing_iso_stageLimitRing D).symm) ∧
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
                    (toAffineEtale.map f)).op ≫
                (ρ U D wU).hom =
                (ρ V D' wV).hom ≫ stageLimitRing.map F τ) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
