/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_19_2_Comparison
public import stacks_project.Chap96.Lemma_96_19_2_RelativeCech

/-!
# Generalities on relative Čech complexes

A 2-commutative square of categories fibred in groupoids over `(Sch/S)_fppf`
induces a morphism `e⁻¹ K^•(f, F) ⟶ K^•(g, e⁻¹ F)`, which is an isomorphism
when the horizontal arrows are equivalences; 2-isomorphic 1-morphisms have
isomorphic relative Čech complexes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Lemma 96.19.2 (1): a 2-commutative square of categories fibred in groupoids
over `(Sch/S)_fppf` induces a morphism of relative Čech complexes
`e⁻¹ K^•(f, F) ⟶ K^•(g, e⁻¹ F)` for an abelian presheaf `F` on `X`. -/
@[stacks 06X9]
def relativeCechMap {V Y : GroupoidsOver S} (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U) (e : Y ⟶ X)
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    RelativeCech.inverseImageComplex e (RelativeCech.complex f F) ⟶
      RelativeCech.complex g (Cech.inverseImage e F) :=
  RelativeCech.map t F

/-- Degree `n` of `relativeCechMap` is the mate of the pullback map along the
1-morphism `V_n ⟶ U_n` induced by the 2-commutative square. -/
theorem relativeCechMap_app {V Y : GroupoidsOver S} (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U)
    (e : Y ⟶ X) (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (relativeCechMap f g h e t F).f n = RelativeCech.map_f t F n :=
  sorry

/-- Lemma 96.19.2 (2): if `h` and `e` are equivalences, then the morphism of
relative Čech complexes in (1) is an isomorphism. -/
@[stacks 06X9]
theorem relativeCechMap_isIso {V Y : GroupoidsOver S} (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U)
    (e : Y ⟶ X) (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hh : BasedFunctor.IsEquivalence (toBasedFunctor h))
    (he : BasedFunctor.IsEquivalence (toBasedFunctor e)) :
    IsIso (relativeCechMap f g h e t F) :=
  sorry

/-- Lemma 96.19.2 (3): if `f, f' : U ⟶ X` are 2-isomorphic, then the associated
relative Čech complexes are isomorphic. -/
@[stacks 06X9]
def relativeCechIso_of_twoIso (f f' : U ⟶ X) (t : f ≅ f')
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    RelativeCech.complex f F ≅ RelativeCech.complex f' F :=
  RelativeCech.isoOfTwoIso t F

/-- Degree `n` of `relativeCechIso_of_twoIso` is pullback along the reindexing of
covering simplices by the 2-isomorphism `t`. -/
theorem relativeCechIso_of_twoIso_hom_app (f f' : U ⟶ X) (t : f ≅ f')
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (relativeCechIso_of_twoIso f f' t F).hom.f n =
      (RelativeCech.isoOfTwoIsoX t F n).hom :=
  sorry

end
