module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_18_1_CoveringSimplex
public import stacks_project.Chap96.Lemma_96_18_1_Cech
public import stacks_project.Chap96.Lemma_96_18_1_Comparison

/-!
# Generalities on Čech complexes of categories fibred in groupoids

A 2-commutative square of categories fibred in groupoids over `(Sch/S)_fppf`
induces a morphism of Čech complexes, which is an isomorphism when the
horizontal arrows are equivalences; 2-isomorphic 1-morphisms have isomorphic
Čech complexes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Lemma 96.18.1 (1): a 2-commutative square of categories fibred in groupoids
over `(Sch/S)_fppf` induces a morphism of Čech complexes
`Cech.complex f F ⟶ Cech.complex g (e⁻¹ F)` for an abelian presheaf `F` on `X`. -/
@[stacks 06X5]
def cechMap {V Y : GroupoidsOver S} (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U) (e : Y ⟶ X)
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Cech.complex f F ⟶ Cech.complex g (Cech.inverseImage e F) :=
  Cech.map t F

/-- Degree `n` of `cechMap` is pullback of global sections along the 1-morphism
`V_n ⟶ U_n` given on objects by `(v_i, y, β_i) ↦ (h(v_i), e(y), t.app v_i ≪≫ e.mapIso β_i)`. -/
theorem cechMap_app {V Y : GroupoidsOver S} (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U)
    (e : Y ⟶ X) (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (cechMap f g h e t F).f n =
      Cech.globalSectionsMap (Cech.coveringMapFunctor t ⦋n⦌)
        ((Cech.apexFunctor f ⦋n⦌).op ⋙ F) :=
  sorry

/-- Lemma 96.18.1 (2): if `h` and `e` are equivalences, then the morphism of
Čech complexes in (1) is an isomorphism. -/
@[stacks 06X5]
theorem cechMap_isIso {V Y : GroupoidsOver S} (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U)
    (e : Y ⟶ X) (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hh : BasedFunctor.IsEquivalence (toBasedFunctor h))
    (he : BasedFunctor.IsEquivalence (toBasedFunctor e)) :
    IsIso (cechMap f g h e t F) := sorry

/-- Lemma 96.18.1 (3): if `f, f' : U ⟶ X` are 2-isomorphic, then the associated
Čech complexes are isomorphic. -/
@[stacks 06X5]
def cechIso_of_twoIso (f f' : U ⟶ X) (t : f ≅ f')
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Cech.complex f F ≅ Cech.complex f' F :=
  Cech.isoOfTwoIso t F

/-- Degree `n` of `cechIso_of_twoIso` is pullback of global sections along the
reindexing of covering simplices by the 2-isomorphism `t`. -/
theorem cechIso_of_twoIso_hom_app (f f' : U ⟶ X) (t : f ≅ f')
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (cechIso_of_twoIso f f' t F).hom.f n =
      Cech.globalSectionsMap (Cech.twoIsoReindex t ⦋n⦌)
        ((Cech.apexFunctor f ⦋n⦌).op ⋙ F) :=
  sorry


end
