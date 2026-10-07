module

public import stacks_project.Chap63.Lemma_63_4_12_Comparison
public import stacks_project.Chap63.Lemma_63_4_12_Stalk

/-!
# Composition of locally quasi-finite lower shriek

For composable locally quasi-finite scheme morphisms `f : X ⟶ Y` and
`g : Y ⟶ Z` there is a canonical functor isomorphism
`(g ∘ f)_! ≅ g_! ∘ f_!` on abelian étale sheaves, with enumerated
coherence for separated composition, mixed composition, stalks,
associativity, and pasted base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [HasCoproducts.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 63.4.12 (1): Let `f : X ⟶ Y` and `g : Y ⟶ Z` be composable locally
quasi-finite morphisms of schemes. Then there is a canonical isomorphism of
functors `(g ∘ f)_! ⟶ g_! ∘ f_!`, i.e.
`lowerShriek (f ≫ g) ≅ lowerShriek f ⋙ lowerShriek g`. -/
@[stacks 0F6T]
def lowerShriekFunctorCompIso :
    lowerShriek (f ≫ g) ≅ lowerShriek f ⋙ lowerShriek g where
  hom := lowerShriekFunctorComp f g
  inv := lowerShriekFunctorCompInv f g
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The objectwise identification `(f ≫ g)_! F ≅ g_! (f_! F)` at an abelian
étale sheaf `F`. -/
def lowerShriekFunctorCompIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f ≫ g)).obj F ≅
      (lowerShriek g).obj ((lowerShriek f).obj F) :=
  (lowerShriekFunctorCompIso f g).app F

/-- The forward map of `lowerShriekFunctorCompIso` is the constructed
composition comparison. -/
theorem lowerShriekFunctorCompIso_hom :
    (lowerShriekFunctorCompIso f g).hom = lowerShriekFunctorComp f g :=
  sorry

/-- The inverse map of `lowerShriekFunctorCompIso` is the dual Čech
descent comparison. -/
theorem lowerShriekFunctorCompIso_inv :
    (lowerShriekFunctorCompIso f g).inv = lowerShriekFunctorCompInv f g :=
  sorry

section separated

variable [IsSeparated f] [IsSeparated g]

/-- Lemma 63.4.12 (2): If `f` and `g` are separated, then the isomorphism
agrees with Lemma 63.3.13. -/
@[stacks 0F6T]
theorem lowerShriekFunctorCompIso_separated :
    lowerShriekFunctorCompIso_separated_left f g =
      lowerShriekFunctorCompIso_separated_right f g :=
  sorry

end separated

section mixed

variable [IsSeparated g]

/-- Lemma 63.4.12 (3): If `g` is separated, then the isomorphism agrees with
Lemma 63.4.11. -/
@[stacks 0F6T]
theorem lowerShriekFunctorCompIso_mixed :
    lowerShriekFunctorCompIso_mixed_left f g =
      lowerShriekFunctorCompIso_mixed_right f g :=
  sorry

end mixed

/-- Lemma 63.4.12 (4): For a geometric point `z̄ : Spec k ⟶ Z` the stalk
diagram of Lemma 63.4.5 for `(g ∘ f)_!` and `g_! ∘ f_!` commutes. -/
@[stacks 0F6T]
theorem lowerShriekFunctorCompIso_stalk (zbar : GeometricPoint Z)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    CommSq (lowerShriekFunctorCompIso_stalk_inner f g zbar F)
      ((toSmallEtalePoint zbar).sheafFiber.map
        ((lowerShriekFunctorCompIso f g).hom.app F))
      (𝟙 ((abelianStalkCoproduct (f ≫ g) zbar).obj F))
      (lowerShriekFunctorCompIso_stalk_outer f g zbar F) :=
  sorry

section assoc

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [HasCoproducts.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 63.4.12 (5): For a third locally quasi-finite morphism `h : Z ⟶ T`
the associativity diagram of composition identifications commutes. -/
@[stacks 0F6T]
theorem lowerShriekFunctorCompIso_assoc :
    lowerShriekFunctorCompIso_assoc_left f g h =
      eqToHom (lowerShriek_assoc f g h) ≫
        lowerShriekFunctorCompIso_assoc_right f g h :=
  sorry

end assoc

section baseChange

variable {X' Y' Z' : Scheme.{u}}
variable (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
variable (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [HasCoproducts.{u} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 63.4.12 (6): For a vertically pasted pair of cartesian squares the
composition isomorphism is compatible with the base-change isomorphisms of
Lemma 63.4.10. -/
@[stacks 0F6T]
theorem lowerShriekFunctorCompIso_baseChange :
    lowerShriekFunctorCompIso_baseChange_inner f g f' g' a b c h_upper h_lower =
      lowerShriekFunctorCompIso_baseChange_outer f g f' g' a b c h_upper h_lower :=
  sorry

end baseChange


end AlgebraicGeometry.Scheme.Etale

end
