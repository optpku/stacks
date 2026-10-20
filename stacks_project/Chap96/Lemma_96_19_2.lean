/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Comparison

/-!
# Generalities on relative Čech complexes

A two-commutative square induces an inverse-image comparison of relative Čech
complexes. Horizontal equivalences make it invertible, and two-isomorphic
covering morphisms have canonically isomorphic relative complexes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

section Square

variable {V Y : GroupoidsOver S} {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
variable (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)

/- Lemma 96.19.2 (1): a two-commutative square induces the canonical comparison
of relative Čech complexes. -/
@[stacks 06X9] #check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.map t F :
  RelativeCech.inverseImageComplex e (RelativeCech.complex f F) ⟶
    RelativeCech.complex g (Cech.inverseImage e F))

#check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.map_app t F n :
  (RelativeCech.map t F).f n = RelativeCech.map_f t F n)

section Equivalences

variable [hh : BasedFunctor.IsEquivalence (toBasedFunctor h)]
variable [he : BasedFunctor.IsEquivalence (toBasedFunctor e)]

/- Lemma 96.19.2 (2): horizontal equivalences make the canonical comparison
an isomorphism. -/
@[stacks 06X9] #check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.map_isIso t F :
  IsIso (RelativeCech.map t F))

end Equivalences
end Square

section TwoIso

variable {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)

/- Lemma 96.19.2 (3): two-isomorphic covering morphisms have canonically
isomorphic relative Čech complexes. -/
@[stacks 06X9] #check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.isoOfTwoIso t F :
  RelativeCech.complex f F ≅ RelativeCech.complex f' F)

#check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.isoOfTwoIso_hom_app t F n :
  (RelativeCech.isoOfTwoIso t F).hom.f n = (RelativeCech.isoOfTwoIsoX t F n).hom)

end TwoIso

/-- The inverse-image comparison of relative Čech complexes attached to a
two-commutative square of categories fibred in groupoids over schemes. -/
def relativeCechMap {V Y : GroupoidsOver S} (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U) (e : Y ⟶ X)
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    RelativeCech.inverseImageComplex e (RelativeCech.complex f F) ⟶
      RelativeCech.complex g (Cech.inverseImage e F) :=
  RelativeCech.map t F

end
