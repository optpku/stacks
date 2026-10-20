module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Truncation
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Object
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Index
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Truncated
public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.ConstHom
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant-source Hom equivalences for simplicial copowers

@stack 018V

This file is the simplicial specialization of the category-generic
`Functor.indexedCoprod.constHom.homEquiv`.  Full and genuinely truncated copowers are direct
specializations.  The restriction of a full copower differs only by the presentation
isomorphism `copower.truncation.iso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace copower.constHom

section Full

variable {U : SSet.{v}} {X : C} {V : SimplicialObject C}

/-- The tensor-Hom equivalence for a simplicial-set copower by a constant simplicial object. -/
@[stacks 018V "constant copower tensor-Hom equivalence"]
def homEquiv (U : SSet.{v}) (X : C) (V : SimplicialObject C)
    [HasCopower U ((const C).obj X)] :
    (copower U ((const C).obj X) ⟶ V) ≃
      (U ⟶ Functor.homFromConst X V) :=
  Functor.indexedCoprod.constHom.homEquiv U X V

/-- The simplicial constant-source tensor-Hom equivalence is natural in the target. -/
@[stacks 018V "constant copower target naturality"]
theorem homEquiv.comp {W : SimplicialObject C}
    [HasCopower U ((const C).obj X)]
    (f : copower U ((const C).obj X) ⟶ V) (g : V ⟶ W) :
    homEquiv U X W (f ≫ g) =
      homEquiv U X V f ≫
        Functor.whiskerRight g (coyoneda.obj (op X)) := sorry

/-- The simplicial constant-source tensor-Hom equivalence is contravariantly natural in the
constant object. -/
@[stacks 018V "constant copower source naturality"]
theorem homEquiv.precomp {Y : C}
    [HasCopower U ((const C).obj X)] [HasCopower U ((const C).obj Y)]
    (f : X ⟶ Y) (g : copower U ((const C).obj Y) ⟶ V) :
    homEquiv U X V (copower.hom U ((const C).map f) ≫ g) =
      homEquiv U Y V g ≫ Functor.whiskerLeft V (coyoneda.map f.op) := sorry

/-- The simplicial constant-source tensor-Hom equivalence is contravariantly natural in its
indexing simplicial set. -/
@[stacks 018V "constant copower index naturality"]
theorem homEquiv.restrict {T : SSet.{v}}
    [HasCopower U ((const C).obj X)] [HasCopower T ((const C).obj X)]
    (a : U ⟶ T) (f : copower T ((const C).obj X) ⟶ V) :
    homEquiv U X V (copower.indexHom ((const C).obj X) a ≫ f) =
      a ≫ homEquiv T X V f := sorry

end Full

section FullUlift

variable {U : SSet.{w}} {X : C} {V : SimplicialObject C}

/-- The cross-universe tensor-Hom equivalence for a simplicial-set copower by a constant
simplicial object.  Both type-valued presheaves are lifted to their common universe. -/
@[stacks 018V "cross-universe constant copower tensor-Hom equivalence"]
def uliftEquiv (U : SSet.{w}) (X : C) (V : SimplicialObject C)
    [HasCopower U ((const C).obj X)] :
    (copower U ((const C).obj X) ⟶ V) ≃
      ((SSet.uliftFunctor.{v, w}).obj U ⟶
        (SSet.uliftFunctor.{w, v}).obj (Functor.homFromConst X V)) :=
  Functor.indexedCoprod.constHom.uliftEquiv U X V

/-- The cross-universe simplicial constant-source tensor-Hom equivalence is natural in the
target. -/
@[stacks 018V "cross-universe constant copower target naturality"]
theorem uliftEquiv.comp {W : SimplicialObject C}
    [HasCopower U ((const C).obj X)]
    (f : copower U ((const C).obj X) ⟶ V) (g : V ⟶ W) :
    uliftEquiv U X W (f ≫ g) =
      uliftEquiv U X V f ≫
        Functor.whiskerRight
          (Functor.whiskerRight g (coyoneda.obj (op X)))
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe simplicial constant-source tensor-Hom equivalence is contravariantly
natural in the constant object. -/
@[stacks 018V "cross-universe constant copower source naturality"]
theorem uliftEquiv.precomp {Y : C}
    [HasCopower U ((const C).obj X)] [HasCopower U ((const C).obj Y)]
    (f : X ⟶ Y) (g : copower U ((const C).obj Y) ⟶ V) :
    uliftEquiv U X V (copower.hom U ((const C).map f) ≫ g) =
      uliftEquiv U Y V g ≫
        Functor.whiskerRight
          (Functor.whiskerLeft V (coyoneda.map f.op))
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe simplicial constant-source tensor-Hom equivalence is contravariantly
natural in its indexing simplicial set. -/
@[stacks 018V "cross-universe constant copower index naturality"]
theorem uliftEquiv.restrict {T : SSet.{w}}
    [HasCopower U ((const C).obj X)] [HasCopower T ((const C).obj X)]
    (a : U ⟶ T) (f : copower T ((const C).obj X) ⟶ V) :
    uliftEquiv U X V (copower.indexHom ((const C).obj X) a ≫ f) =
      (SSet.uliftFunctor.{v, w}).map a ≫ uliftEquiv T X V f := sorry

end FullUlift

end copower.constHom

namespace copower.truncation.constHom

section Restricted

variable {n : ℕ} {U : SSet.{v}} {X : C} {V : SimplicialObject C}

/-- The tensor-Hom equivalence for the restriction of a full constant simplicial copower.
Its only additional content over the generic theorem is the restriction presentation
isomorphism. -/
@[stacks 018V "restricted constant copower tensor-Hom equivalence"]
def homEquiv (n : ℕ) (U : SSet.{v}) (X : C) (V : SimplicialObject C)
    [HasCopower U ((const C).obj X)] :
    ((truncation n).obj (copower U ((const C).obj X)) ⟶ (truncation n).obj V) ≃
      ((SSet.truncation n).obj U ⟶
        Functor.homFromConst X ((truncation n).obj V)) :=
  ((copower.truncation.iso n U ((const C).obj X)).homCongr (Iso.refl _)).trans
    (Functor.indexedCoprod.constHom.homEquiv ((SSet.truncation n).obj U) X
      ((truncation n).obj V))

/-- The restricted constant-source tensor-Hom equivalence is natural in the full target. -/
@[stacks 018V "restricted constant copower target naturality"]
theorem homEquiv.comp {W : SimplicialObject C}
    [HasCopower U ((const C).obj X)]
    (f : (truncation n).obj (copower U ((const C).obj X)) ⟶ (truncation n).obj V)
    (g : V ⟶ W) :
    homEquiv n U X W (f ≫ (truncation n).map g) =
      homEquiv n U X V f ≫
        Functor.whiskerRight ((truncation n).map g) (coyoneda.obj (op X)) := sorry

/-- The restricted constant-source tensor-Hom equivalence is contravariantly natural in the
constant object. -/
@[stacks 018V "restricted constant copower source naturality"]
theorem homEquiv.precomp {Y : C}
    [HasCopower U ((const C).obj X)] [HasCopower U ((const C).obj Y)]
    (f : X ⟶ Y)
    (g : (truncation n).obj (copower U ((const C).obj Y)) ⟶ (truncation n).obj V) :
    homEquiv n U X V
        ((truncation n).map (copower.hom U ((const C).map f)) ≫ g) =
      homEquiv n U Y V g ≫
        Functor.whiskerLeft ((truncation n).obj V) (coyoneda.map f.op) := sorry

/-- The restricted constant-source tensor-Hom equivalence is contravariantly natural in the
truncated indexing object. -/
@[stacks 018V "restricted constant copower index naturality"]
theorem homEquiv.restrict {T : SSet.{v}}
    [HasCopower U ((const C).obj X)] [HasCopower T ((const C).obj X)]
    (a : (SSet.truncation n).obj U ⟶ (SSet.truncation n).obj T)
    (f : (truncation n).obj (copower T ((const C).obj X)) ⟶ (truncation n).obj V) :
    homEquiv n U X V (copower.truncation.indexHom n ((const C).obj X) a ≫ f) =
      a ≫ homEquiv n T X V f := sorry

end Restricted

section RestrictedUlift

variable {n : ℕ} {U : SSet.{w}} {X : C} {V : SimplicialObject C}

/-- The cross-universe tensor-Hom equivalence for the restriction of a full constant simplicial
copower. -/
@[stacks 018V "cross-universe restricted constant copower tensor-Hom equivalence"]
def uliftEquiv (n : ℕ) (U : SSet.{w}) (X : C) (V : SimplicialObject C)
    [HasCopower U ((const C).obj X)] :
    ((truncation n).obj (copower U ((const C).obj X)) ⟶ (truncation n).obj V) ≃
      ((SSet.Truncated.uliftFunctor.{v, w} n).obj ((SSet.truncation n).obj U) ⟶
        (SSet.Truncated.uliftFunctor.{w, v} n).obj
          (Functor.homFromConst X ((truncation n).obj V))) :=
  ((copower.truncation.iso n U ((const C).obj X)).homCongr (Iso.refl _)).trans
    (Functor.indexedCoprod.constHom.uliftEquiv ((SSet.truncation n).obj U) X
      ((truncation n).obj V))

/-- The cross-universe restricted constant-source tensor-Hom equivalence is natural in the full
target. -/
@[stacks 018V "cross-universe restricted constant copower target naturality"]
theorem uliftEquiv.comp {W : SimplicialObject C}
    [HasCopower U ((const C).obj X)]
    (f : (truncation n).obj (copower U ((const C).obj X)) ⟶ (truncation n).obj V)
    (g : V ⟶ W) :
    uliftEquiv n U X W (f ≫ (truncation n).map g) =
      uliftEquiv n U X V f ≫
        Functor.whiskerRight
          (Functor.whiskerRight ((truncation n).map g) (coyoneda.obj (op X)))
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe restricted constant-source tensor-Hom equivalence is contravariantly
natural in the constant object. -/
@[stacks 018V "cross-universe restricted constant copower source naturality"]
theorem uliftEquiv.precomp {Y : C}
    [HasCopower U ((const C).obj X)] [HasCopower U ((const C).obj Y)]
    (f : X ⟶ Y)
    (g : (truncation n).obj (copower U ((const C).obj Y)) ⟶ (truncation n).obj V) :
    uliftEquiv n U X V
        ((truncation n).map (copower.hom U ((const C).map f)) ≫ g) =
      uliftEquiv n U Y V g ≫
        Functor.whiskerRight
          (Functor.whiskerLeft ((truncation n).obj V) (coyoneda.map f.op))
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe restricted constant-source tensor-Hom equivalence is contravariantly
natural in the truncated indexing object. -/
@[stacks 018V "cross-universe restricted constant copower index naturality"]
theorem uliftEquiv.restrict {T : SSet.{w}}
    [HasCopower U ((const C).obj X)] [HasCopower T ((const C).obj X)]
    (a : (SSet.truncation n).obj U ⟶ (SSet.truncation n).obj T)
    (f : (truncation n).obj (copower T ((const C).obj X)) ⟶ (truncation n).obj V) :
    uliftEquiv n U X V (copower.truncation.indexHom n ((const C).obj X) a ≫ f) =
      (SSet.Truncated.uliftFunctor.{v, w} n).map a ≫
        uliftEquiv n T X V f := sorry

end RestrictedUlift

end copower.truncation.constHom

namespace Truncated.copower.constHom

section Truncated

variable {n : ℕ} {U : SSet.Truncated.{v} n} {X : C}
variable {V : SimplicialObject.Truncated C n}

/-- The tensor-Hom equivalence for a genuinely truncated copower by a constant object. -/
@[stacks 018V "truncated constant copower tensor-Hom equivalence"]
def homEquiv (U : SSet.Truncated.{v} n) (X : C)
    (V : SimplicialObject.Truncated C n)
    [Truncated.HasCopower U ((Functor.const _).obj X)] :
    (Truncated.copower U ((Functor.const _).obj X) ⟶ V) ≃
      (U ⟶ Functor.homFromConst X V) :=
  Functor.indexedCoprod.constHom.homEquiv U X V

/-- The truncated constant-source tensor-Hom equivalence is natural in the target. -/
@[stacks 018V "truncated constant copower target naturality"]
theorem homEquiv.comp {W : SimplicialObject.Truncated C n}
    [Truncated.HasCopower U ((Functor.const _).obj X)]
    (f : Truncated.copower U ((Functor.const _).obj X) ⟶ V) (g : V ⟶ W) :
    homEquiv U X W (f ≫ g) =
      homEquiv U X V f ≫
        Functor.whiskerRight g (coyoneda.obj (op X)) := sorry

/-- The truncated constant-source tensor-Hom equivalence is contravariantly natural in the
constant object. -/
@[stacks 018V "truncated constant copower source naturality"]
theorem homEquiv.precomp {Y : C}
    [Truncated.HasCopower U ((Functor.const _).obj X)]
    [Truncated.HasCopower U ((Functor.const _).obj Y)]
    (f : X ⟶ Y) (g : Truncated.copower U ((Functor.const _).obj Y) ⟶ V) :
    homEquiv U X V (Truncated.copower.hom U ((Functor.const _).map f) ≫ g) =
      homEquiv U Y V g ≫ Functor.whiskerLeft V (coyoneda.map f.op) := sorry

/-- The truncated constant-source tensor-Hom equivalence is contravariantly natural in its
indexing truncated simplicial set. -/
@[stacks 018V "truncated constant copower index naturality"]
theorem homEquiv.restrict {T : SSet.Truncated.{v} n}
    [Truncated.HasCopower U ((Functor.const _).obj X)]
    [Truncated.HasCopower T ((Functor.const _).obj X)]
    (a : U ⟶ T) (f : Truncated.copower T ((Functor.const _).obj X) ⟶ V) :
    homEquiv U X V (Truncated.copower.indexHom ((Functor.const _).obj X) a ≫ f) =
      a ≫ homEquiv T X V f := sorry

end Truncated

section TruncatedUlift

variable {n : ℕ} {U : SSet.Truncated.{w} n} {X : C}
variable {V : SimplicialObject.Truncated C n}

/-- The cross-universe tensor-Hom equivalence for a genuinely truncated copower by a constant
object. -/
@[stacks 018V "cross-universe truncated constant copower tensor-Hom equivalence"]
def uliftEquiv (U : SSet.Truncated.{w} n) (X : C)
    (V : SimplicialObject.Truncated C n)
    [Truncated.HasCopower U ((Functor.const _).obj X)] :
    (Truncated.copower U ((Functor.const _).obj X) ⟶ V) ≃
      ((SSet.Truncated.uliftFunctor.{v, w} n).obj U ⟶
        (SSet.Truncated.uliftFunctor.{w, v} n).obj (Functor.homFromConst X V)) :=
  Functor.indexedCoprod.constHom.uliftEquiv U X V

/-- The cross-universe truncated constant-source tensor-Hom equivalence is natural in the
target. -/
@[stacks 018V "cross-universe truncated constant copower target naturality"]
theorem uliftEquiv.comp {W : SimplicialObject.Truncated C n}
    [Truncated.HasCopower U ((Functor.const _).obj X)]
    (f : Truncated.copower U ((Functor.const _).obj X) ⟶ V) (g : V ⟶ W) :
    uliftEquiv U X W (f ≫ g) =
      uliftEquiv U X V f ≫
        Functor.whiskerRight
          (Functor.whiskerRight g (coyoneda.obj (op X)))
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe truncated constant-source tensor-Hom equivalence is contravariantly
natural in the constant object. -/
@[stacks 018V "cross-universe truncated constant copower source naturality"]
theorem uliftEquiv.precomp {Y : C}
    [Truncated.HasCopower U ((Functor.const _).obj X)]
    [Truncated.HasCopower U ((Functor.const _).obj Y)]
    (f : X ⟶ Y) (g : Truncated.copower U ((Functor.const _).obj Y) ⟶ V) :
    uliftEquiv U X V (Truncated.copower.hom U ((Functor.const _).map f) ≫ g) =
      uliftEquiv U Y V g ≫
        Functor.whiskerRight
          (Functor.whiskerLeft V (coyoneda.map f.op))
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe truncated constant-source tensor-Hom equivalence is contravariantly
natural in its indexing truncated simplicial set. -/
@[stacks 018V "cross-universe truncated constant copower index naturality"]
theorem uliftEquiv.restrict {T : SSet.Truncated.{w} n}
    [Truncated.HasCopower U ((Functor.const _).obj X)]
    [Truncated.HasCopower T ((Functor.const _).obj X)]
    (a : U ⟶ T) (f : Truncated.copower T ((Functor.const _).obj X) ⟶ V) :
    uliftEquiv U X V (Truncated.copower.indexHom ((Functor.const _).obj X) a ≫ f) =
      (SSet.Truncated.uliftFunctor.{v, w} n).map a ≫ uliftEquiv T X V f := sorry

end TruncatedUlift

end Truncated.copower.constHom

end CategoryTheory.SimplicialObject
