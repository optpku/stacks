/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UniversallyInjectiveIntegral

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [UniversallyInjective f] [IsIntegralHom f]

/- Lemma 59.44.5 -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallEtale.pushforward_reflectsMonomorphisms f :
    (smallMorphism f).pushforward.ReflectsMonomorphisms)

/- Lemma 59.44.5 (2) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallEtale.pushforward_reflectsEpimorphisms f :
    (smallMorphism f).pushforward.ReflectsEpimorphisms)

/- Lemma 59.44.5 (3) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallEtale.pushforward_preservesFiniteConnectedColimits f :
    PreservesFiniteConnectedColimits (smallMorphism f).pushforward)

/- Lemma 59.44.5 (4) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.Scheme.SmallEtaleDirectImage.preservesLocallySurjective_of_isIntegralHom f :
    (Scheme.smallEtaleDirectImage f).PreservesLocallySurjective)

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Lemma 59.44.5 (5) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallAbelianPushforward.preservesEpimorphisms_of_isIntegralHom f :
    (AlgebraicGeometry.smallAbelianPushforward f).PreservesEpimorphisms)

/- Lemma 59.44.5 (6) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallEtale.pushforward_counit_epi f :
    ∀ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      Epi ((smallMorphism f).adjunction.counit.app F))

/- Lemma 59.44.5 (7) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallAbelianPushforward.counit_epi_of_isIntegralHom f :
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w},
      Epi (((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
        AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).counit.app F))

/- Lemma 59.44.5 (8) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallEtale.pushforward_faithful f :
    (smallMorphism f).pushforward.Faithful)

/- Lemma 59.44.5 (9) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallAbelianPushforward.faithful_of_isIntegralHom f :
    (AlgebraicGeometry.smallAbelianPushforward f).Faithful)

/- Lemma 59.44.5 (10) and (11) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallAbelianPushforward.exact_of_isIntegralHom f :
    exactFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{w})
      (AlgebraicGeometry.smallAbelianPushforward f))

/- Lemma 59.44.5 (12) -/
@[stacks 04DX] #check
  (AlgebraicGeometry.SmallEtale.pullback_isAlmostCocontinuous f :
    Functor.IsAlmostCocontinuous (Scheme.smallEtalePullback f)
      Y.smallEtaleTopology X.smallEtaleTopology)
