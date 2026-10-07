module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_11_1_Component
public import stacks_project.Chap85.Lemma_85_11_1_Flat

/-!
# Lemma 85.11.1

An augmentation of ringed simplicial sites is flat if and only if every
degree-`n` component morphism is flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

universe u v w uD vD

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsSiteDiagram C J] (O : Sheaf (topology C J) RingCat.{w})
variable {D : RingedSite.{uD, vD, w}}
variable [UnivLE.{max u v, w}]
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable (a : ToposHom (totalRingedSite C J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (augmentationComponent C J O a n).structureMap).IsRightAdjoint]

/-- Lemma 85.11.1: the morphism `a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` of ringed topoi is
flat if and only if `a_n : (Sh(C_n), O_n) ⟶ (Sh(D), O_D)` is flat for every
`n : SimplexCategory`. Here `a_n` is the composite `a ∘ g_n` of `a` with the degree-`n`
inclusion `g_n`, and `a^♯` is `a.directStructureMap`. -/
@[stacks 0DH3]
theorem augmentation_isFlat_iff :
    ToposHom.IsFlat a ↔
      ∀ n : SimplexCategory, ToposHom.IsFlat (augmentationComponent C J O a n) :=
  sorry

end CategoryTheory.SimplicialSites
