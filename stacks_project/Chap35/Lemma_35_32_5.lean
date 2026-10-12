/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 35.32.5 (1): an étale-local-on-source-and-target property holds for `f` exactly
when it holds on a suitable étale square around every point of the source. -/
@[stacks 04R1] #check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.iff_exists :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P]
      {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      P f ↔
        ∀ x : X, ∃ (U : X.Etale) (V : Y.Etale) (h : U.left ⟶ V.left) (u : U.left),
          U.hom u = x ∧ CategoryTheory.CommSq h U.hom V.hom f ∧ P h)

/- Lemma 35.32.5 (2): an étale-local-on-source-and-target property holds for `f` exactly
when it holds on the top map of every commutative square with étale vertical maps. -/
@[stacks 04R1] #check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.iff_forall_square :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P]
      {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      P f ↔ ∀ (U : X.Etale) (V : Y.Etale) (h : U.left ⟶ V.left),
        CategoryTheory.CommSq h U.hom V.hom f → P h)

/- Lemma 35.32.5 (3): an étale-local-on-source-and-target property holds for `f` exactly
when it holds on the top map of some étale square whose left vertical map is surjective. -/
@[stacks 04R1] #check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.iff_exists_surjective_square :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P]
      {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      P f ↔ ∃ (U : X.Etale) (V : Y.Etale) (h : U.left ⟶ V.left),
        AlgebraicGeometry.Surjective U.hom ∧
          CategoryTheory.CommSq h U.hom V.hom f ∧ P h)

/- Lemma 35.32.5 (4): an étale-local-on-source-and-target property holds for `f` exactly
when it holds after base change along every member of some étale cover of the target. -/
@[stacks 04R1] #check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.iff_exists_targetCover :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P]
      {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : Y.Cover.{u} AlgebraicGeometry.Scheme.etalePrecoverage,
        ∀ i : 𝒰.I₀, P (𝒰.pullbackHom f i))

/- Lemma 35.32.5 (5): an étale-local-on-source-and-target property holds for `f` exactly
when every member of some étale cover of the source has property `P` after composition with
`f`. -/
@[stacks 04R1] #check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.iff_exists_sourceCover :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P]
      {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : X.Cover.{u} AlgebraicGeometry.Scheme.etalePrecoverage,
        ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f))

/- Lemma 35.32.5 (6): an étale-local-on-source-and-target property holds for `f` exactly
when, after some étale cover of the target, each base change admits an étale source cover on
whose composites to the target-cover member property `P` holds. -/
@[stacks 04R1] #check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.iff_exists_targetSourceCovers :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P]
      {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      P f ↔ ∃ 𝒰 : Y.Cover.{u} AlgebraicGeometry.Scheme.etalePrecoverage, ∀ i : 𝒰.I₀,
        ∃ 𝒱 : ((𝒰.pullback₁ f).X i).Cover.{u} AlgebraicGeometry.Scheme.etalePrecoverage,
          ∀ j : 𝒱.I₀, P (𝒱.f j ≫ 𝒰.pullbackHom f i))
