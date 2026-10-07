module

public import Mathlib.CategoryTheory.Subobject.FactorThru
public import stacks_project.Chap63.Lemma_63_3_12_Comparison
public import stacks_project.Chap63.Lemma_63_3_13
public import stacks_project.Chap63.Lemma_63_3_13_LowerShriek

/-!
# Composition isomorphism for underived étale lower shriek

The unique factorization of `etaleLowerShriekCompι` through
`etaleLowerShriekι (f ≫ g)` packages the subsheaf identification of
Lemma 63.3.13 as a functor isomorphism `f_! ⋙ g_! ≅ (f ≫ g)_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsSeparated f] [LocallyOfFiniteType f]
variable [IsSeparated g] [LocallyOfFiniteType g]

/-- The pushforward comparison `g_! ∘ f_! ⟶ (f ≫ g)_*` factors through the
compact-support inclusion `(f ≫ g)_! ⟶ (f ≫ g)_*`. -/
theorem etaleLowerShriekComp_factors :
    MonoOver.Factors (MonoOver.mk (etaleLowerShriekι (f ≫ g)))
      (etaleLowerShriekCompι f g) :=
  sorry

/-- The canonical comparison `f_! ⋙ g_! ⟶ (f ≫ g)_!` obtained by uniquely
factoring `etaleLowerShriekCompι` through `etaleLowerShriekι (f ≫ g)`. -/
def etaleLowerShriekComp :
    etaleLowerShriek f ⋙ etaleLowerShriek g ⟶ etaleLowerShriek (f ≫ g) :=
  MonoOver.factorThru (MonoOver.mk (etaleLowerShriekι (f ≫ g)))
    (etaleLowerShriekCompι f g) (etaleLowerShriekComp_factors f g)

/-- The comparison fills the triangle with the compact-support inclusion of
`(f ≫ g)_!`. -/
theorem etaleLowerShriekComp_ι :
    etaleLowerShriekComp f g ≫ etaleLowerShriekι (f ≫ g) =
      etaleLowerShriekCompι f g :=
  sorry

/-- Any morphism making the compact-support triangle commute equals the
canonical comparison. -/
theorem etaleLowerShriekComp_lift_unique
    (α : etaleLowerShriek f ⋙ etaleLowerShriek g ⟶ etaleLowerShriek (f ≫ g))
    (hα : α ≫ etaleLowerShriekι (f ≫ g) = etaleLowerShriekCompι f g) :
    α = etaleLowerShriekComp f g :=
  sorry

/-- The comparison `f_! ⋙ g_! ⟶ (f ≫ g)_!` is an isomorphism. -/
instance etaleLowerShriekComp_isIso : IsIso (etaleLowerShriekComp f g) :=
  sorry

/-- The functor isomorphism `f_! ⋙ g_! ≅ (f ≫ g)_!`. -/
def etaleLowerShriekCompIso :
    etaleLowerShriek f ⋙ etaleLowerShriek g ≅ etaleLowerShriek (f ≫ g) :=
  asIso (etaleLowerShriekComp f g)

/-- The forward map of `etaleLowerShriekCompIso` is the compact-support
composition comparison. -/
theorem etaleLowerShriekCompIso_hom :
    (etaleLowerShriekCompIso f g).hom = etaleLowerShriekComp f g :=
  sorry

section assoc

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [IsSeparated h] [LocallyOfFiniteType h]

/-- `etaleLowerShriek` depends only on the underlying morphism, so it is
unchanged by reassociation of a triple composite. -/
theorem etaleLowerShriek_assoc :
    etaleLowerShriek ((f ≫ g) ≫ h) = etaleLowerShriek (f ≫ g ≫ h) :=
  sorry

/-- Left-then-bottom path of the associativity square: apply
`(etaleLowerShriekCompIso (f ≫ g) h).inv`, whisker
`(etaleLowerShriekCompIso f g).inv` on the right, then the functor
associator. -/
def etaleLowerShriekCompIso_assoc_left :
    etaleLowerShriek ((f ≫ g) ≫ h) ⟶
      etaleLowerShriek f ⋙ etaleLowerShriek g ⋙ etaleLowerShriek h :=
  (etaleLowerShriekCompIso (f ≫ g) h).inv ≫
    whiskerRight (etaleLowerShriekCompIso f g).inv (etaleLowerShriek h) ≫
    (associator (etaleLowerShriek f) (etaleLowerShriek g) (etaleLowerShriek h)).hom

/-- Top-then-right path of the associativity square: apply
`(etaleLowerShriekCompIso f (g ≫ h)).inv`, then whisker
`(etaleLowerShriekCompIso g h).inv` on the left. -/
def etaleLowerShriekCompIso_assoc_right :
    etaleLowerShriek (f ≫ g ≫ h) ⟶
      etaleLowerShriek f ⋙ etaleLowerShriek g ⋙ etaleLowerShriek h :=
  (etaleLowerShriekCompIso f (g ≫ h)).inv ≫
    whiskerLeft (etaleLowerShriek f) (etaleLowerShriekCompIso g h).inv

end assoc

section baseChange_vcomp

variable {X' Y' Z' : Scheme.{u}}
variable (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
variable (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
variable [IsSeparated f'] [LocallyOfFiniteType f']
variable [IsSeparated g'] [LocallyOfFiniteType g']

/-- Two-step path of the pasted base-change square: the composition
identification of `f` and `g`, then the lower base change of `g`, then the
upper base change of `f`, with functor associators. -/
def etaleLowerShriekCompIso_baseChange_vcomp_inner :
    etaleLowerShriek (f ≫ g) ⋙ etaleAbelianSheafPullback a ⟶
      etaleAbelianSheafPullback c ⋙ etaleLowerShriek f' ⋙ etaleLowerShriek g' :=
  whiskerRight (etaleLowerShriekCompIso f g).inv (etaleAbelianSheafPullback a) ≫
    (associator (etaleLowerShriek f) (etaleLowerShriek g)
        (etaleAbelianSheafPullback a)).hom ≫
    whiskerLeft (etaleLowerShriek f) (etaleLowerShriekBaseChange g a g' b h_lower) ≫
    (associator (etaleLowerShriek f) (etaleAbelianSheafPullback b)
        (etaleLowerShriek g')).inv ≫
    whiskerRight (etaleLowerShriekBaseChange f b f' c h_upper) (etaleLowerShriek g') ≫
    (associator (etaleAbelianSheafPullback c) (etaleLowerShriek f')
        (etaleLowerShriek g')).hom

/-- Outer path of the pasted base-change square: base change of `f ≫ g` along
the pasted cartesian square, then the composition identification of `f'` and
`g'`. -/
def etaleLowerShriekCompIso_baseChange_vcomp_outer :
    etaleLowerShriek (f ≫ g) ⋙ etaleAbelianSheafPullback a ⟶
      etaleAbelianSheafPullback c ⋙ etaleLowerShriek f' ⋙ etaleLowerShriek g' :=
  etaleLowerShriekBaseChange (f ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) ≫
    whiskerLeft (etaleAbelianSheafPullback c) (etaleLowerShriekCompIso f' g').inv

end baseChange_vcomp

end AlgebraicGeometry.Scheme.Etale

end
