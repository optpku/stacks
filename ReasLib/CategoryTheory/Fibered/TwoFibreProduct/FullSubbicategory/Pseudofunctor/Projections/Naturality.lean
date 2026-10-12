/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Projections.Comparison

/-!
# Coherence of full-subbicategory two-fibre-product projections

The `2`-cell naturality, identity, and composition laws for the endpoint comparisons.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

/-- The first-projection comparisons are natural for the `2`-morphism action of the
left-endpoint projection pseudofunctor. -/
theorem pseudofunctor.fstIso.naturality.map₂
    {S T : Bicategory.Cospan P.FullSubbicategory}
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (pseudofunctor P).map₂ Gamma ▷ fst T.fst T.snd ≫
        (pseudofunctor.fstIso phi).hom =
      (pseudofunctor.fstIso psi).hom ≫
        fst S.fst S.snd ◁
          (Bicategory.Cospan.leftProjection P.FullSubbicategory).map₂ Gamma := sorry

/-- The first-projection comparisons respect the identity comparison cells of the
two-fibre-product and left-endpoint pseudofunctors. -/
theorem pseudofunctor.fstIso.id
    (S : Bicategory.Cospan P.FullSubbicategory) :
    (pseudofunctor.fstIso (𝟙 S)).hom ≫
          fst S.fst S.snd ◁
            ((Bicategory.Cospan.leftProjection P.FullSubbicategory).mapId S).hom =
      ((pseudofunctor P).mapId S).hom ▷ fst S.fst S.snd ≫
        (Bicategory.leftUnitor (a := (pseudofunctor P).obj S) (b := S.left)
          (fst S.fst S.snd)).hom ≫
          (Bicategory.rightUnitor (a := (pseudofunctor P).obj S) (b := S.left)
            (fst S.fst S.snd)).inv := sorry

/-- The first-projection comparisons respect the composition comparison cells of the
two-fibre-product and left-endpoint pseudofunctors. -/
theorem pseudofunctor.fstIso.comp
    {R S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    (pseudofunctor.fstIso (psi ≫ phi)).hom ≫
          fst R.fst R.snd ◁
            ((Bicategory.Cospan.leftProjection P.FullSubbicategory).mapComp psi phi).hom =
      ((pseudofunctor P).mapComp psi phi).hom ▷ fst T.fst T.snd ≫
        (α_ _ _ _).hom ≫
          (pseudofunctor P).map psi ◁ (pseudofunctor.fstIso phi).hom ≫
            (α_ _ _ _).inv ≫
              (pseudofunctor.fstIso psi).hom ▷
                (Bicategory.Cospan.leftProjection P.FullSubbicategory).map phi ≫
                (α_ _ _ _).hom := sorry

/-- The second-projection comparisons are natural for the `2`-morphism action of the
right-endpoint projection pseudofunctor. -/
theorem pseudofunctor.sndIso.naturality.map₂
    {S T : Bicategory.Cospan P.FullSubbicategory}
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (pseudofunctor P).map₂ Gamma ▷ snd T.fst T.snd ≫
        (pseudofunctor.sndIso phi).hom =
      (pseudofunctor.sndIso psi).hom ≫
        snd S.fst S.snd ◁
          (Bicategory.Cospan.rightProjection P.FullSubbicategory).map₂ Gamma := sorry

/-- The second-projection comparisons respect the identity comparison cells of the
two-fibre-product and right-endpoint pseudofunctors. -/
theorem pseudofunctor.sndIso.id
    (S : Bicategory.Cospan P.FullSubbicategory) :
    (pseudofunctor.sndIso (𝟙 S)).hom ≫
          snd S.fst S.snd ◁
            ((Bicategory.Cospan.rightProjection P.FullSubbicategory).mapId S).hom =
      ((pseudofunctor P).mapId S).hom ▷ snd S.fst S.snd ≫
        (Bicategory.leftUnitor (a := (pseudofunctor P).obj S) (b := S.right)
          (snd S.fst S.snd)).hom ≫
          (Bicategory.rightUnitor (a := (pseudofunctor P).obj S) (b := S.right)
            (snd S.fst S.snd)).inv := sorry

/-- The second-projection comparisons respect the composition comparison cells of the
two-fibre-product and right-endpoint pseudofunctors. -/
theorem pseudofunctor.sndIso.comp
    {R S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    (pseudofunctor.sndIso (psi ≫ phi)).hom ≫
          snd R.fst R.snd ◁
            ((Bicategory.Cospan.rightProjection P.FullSubbicategory).mapComp psi phi).hom =
      ((pseudofunctor P).mapComp psi phi).hom ▷ snd T.fst T.snd ≫
        (α_ _ _ _).hom ≫
          (pseudofunctor P).map psi ◁ (pseudofunctor.sndIso phi).hom ≫
            (α_ _ _ _).inv ≫
              (pseudofunctor.sndIso psi).hom ▷
                (Bicategory.Cospan.rightProjection P.FullSubbicategory).map phi ≫
                (α_ _ _ _).hom := sorry

end TwoFibreProduct

end CategoryTheory
