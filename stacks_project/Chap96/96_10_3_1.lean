module

public import stacks_project.Chap96.«96_10_3_1_Comparison»
public import stacks_project.Chap96.«96_10_3_1_Restriction»
import StacksCheckRecall

/-!
# 96.10.3.1

Restriction of the CFG étale pushforward of a sheaf on `S_F` to the small
étale site of `G` is canonically identified with the small étale pushforward
of the restricted sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids

universe u

variable {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G)
variable (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1)))
variable [HasSheafify F.toGroupoids.etaleTopology (Type (u + 1))]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.HasPointwiseRightKanExtension P]

/- 96.10.3.1 The identification compareBigSmall f ℱ is the canonical isomorphism
(f_* ℱ)|_{G_étale} = f_small,* (ℱ|_{F_étale}) of sheaves on G_étale, obtained by
comparing restriction along smallEtaleToGroupoids with sheafPushforwardType f.
When ℱ is an 𝒪-module the same identification is an isomorphism of 𝒪_G-modules. -/
@[stacks 075M]
#check (compareBigSmall f ℱ :
    (restrictEtale G).obj ((etalePushforward f).obj ℱ) ≅
      (sheafPushforwardType f).obj ((restrictEtale F).obj ℱ))
