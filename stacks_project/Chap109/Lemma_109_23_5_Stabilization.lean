module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_20_3_Substack
public import stacks_project.Chap109.Lemma_109_22_7_Substack
public import stacks_project.Chap109.Lemma_109_23_4_Contraction

/-!
# Stabilization as a 1-morphism of algebraic stacks of curves

A prestable family of curves of genus at least two determines a stable family
by contraction. Compatibility with base change and isomorphisms promotes that
assignment to a 1-morphism of algebraic stacks over `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of prestable families of curves of genus `g` remains
fibred in groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_prestableOfGenus (g : ℕ) (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((prestableOfGenus g S).ι ⋙ p S) :=
  sorry

/-- The structure morphism of a family of curves, transported along the
identification of its base with the identity morphism of `S`. -/
def asIdentityBase {S : Scheme.{u}} (P : Obj S)
    (hbase : base P = Over.mk (𝟙 S)) :
    space P ⟶ ofOver (Over.mk (𝟙 S)) :=
  hom P ≫ (ofOverFunctor S).map (eqToHom hbase)

/-- `asIdentityBase P hbase` is the composite of `hom P` with the `ofOver`
image of `eqToHom hbase`. -/
theorem asIdentityBase_spec {S : Scheme.{u}} (P : Obj S)
    (hbase : base P = Over.mk (𝟙 S)) :
    asIdentityBase P hbase = hom P ≫ (ofOverFunctor S).map (eqToHom hbase) :=
  sorry

/-- Package an identity-base prestable family of curves of genus `g` as an
object of `prestableOfGenus g S`. -/
def prestableMk {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) {g : ℕ} [IsFamily f] [Prestable f]
    (hgenus : SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne f)) :
    (prestableOfGenus g S).FullSubcategory where
  obj := mk f
  property := sorry

/-- The underlying family of `prestableMk f hgenus` is `mk f`. -/
theorem prestableMk_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) {g : ℕ} [IsFamily f] [Prestable f]
    (hgenus : SheafOfModules.IsFiniteLocallyFreeOfRank g
      (higherDirectImageOne f)) :
    (prestableMk f hgenus).obj = mk f :=
  sorry

/-- A 1-morphism of groupoids over `Over S` sends identity-base objects to
identity-base objects. -/
theorem map_eq_identityBase {g : ℕ} {S : Scheme.{u}}
    (F : ofObjectProperty (prestableOfGenus g S) ⟶
      ofObjectProperty (stableOfGenus g S))
    (P : (prestableOfGenus g S).FullSubcategory)
    (hbase : base P.obj = Over.mk (𝟙 S)) :
    base ((Groupoids.toFunctor F).obj P).obj = Over.mk (𝟙 S) :=
  sorry

/-- A 1-morphism of algebraic stacks from prestable genus-`g` curves to the
stable moduli stack is a stabilization when it sends every identity-base
prestable family of genus `g` to a contraction onto a stable family. -/
def IsStabilization {g : ℕ} (hg : 2 ≤ g) {S : Scheme.{u}}
    (F : ofObjectProperty (prestableOfGenus g S) ⟶
      ofObjectProperty (stableOfGenus g S)) : Prop :=
  ∀ {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [IsFamily f] [Prestable f]
    (hgenus : SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne f)),
    ∃ (c : space (mk f) ⟶
        space ((Groupoids.toFunctor F).obj (prestableMk f hgenus)).obj)
      (hc : c ≫ asIdentityBase
          ((Groupoids.toFunctor F).obj (prestableMk f hgenus)).obj
          (map_eq_identityBase F (prestableMk f hgenus) (mk_base f)) =
        asIdentityBase (mk f) (mk_base f)),
      IsContractionToStable c hc

namespace IsStabilization

/-- A stabilization 1-morphism sends every identity-base prestable genus-`g`
family to a contraction onto the identity-base structure morphism of its
image. -/
theorem iff {g : ℕ} (hg : 2 ≤ g) {S : Scheme.{u}}
    (F : ofObjectProperty (prestableOfGenus g S) ⟶
      ofObjectProperty (stableOfGenus g S)) :
    IsStabilization hg F ↔
      ∀ {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
        [IsFamily f] [Prestable f]
        (hgenus : SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne f)),
        ∃ (c : space (mk f) ⟶
            space ((Groupoids.toFunctor F).obj (prestableMk f hgenus)).obj)
          (hc : c ≫ asIdentityBase
              ((Groupoids.toFunctor F).obj (prestableMk f hgenus)).obj
              (map_eq_identityBase F (prestableMk f hgenus) (mk_base f)) =
            asIdentityBase (mk f) (mk_base f)),
          IsContractionToStable c hc :=
  sorry

end IsStabilization

/-- For `g ≥ 2` there is a morphism of algebraic stacks from
`𝒞urves^{prestable}_g` to `ℳ̄_g` sending a prestable family of genus `g` to
an associated stable contraction. -/
theorem exists_stabilization (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    ∃ F : ofObjectProperty (prestableOfGenus g S) ⟶
        ofObjectProperty (stableOfGenus g S),
      IsStabilization hg F :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
