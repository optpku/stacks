/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Yoneda
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# Covariant bicategorical representables

This file provides the covariant companion to `Bicategory.yoneda₀`. For an object `x` of a
bicategory `B`, the pseudofunctor `Bicategory.coyoneda₀ x` sends `y` to the hom-category
`x ⟶ y`; `1`- and `2`-morphisms act by postcomposition.

Keeping this construction independent of bicategorical limits makes it available to any
representability argument involving covariant hom-pseudofunctors.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- The prelax core of the covariant bicategorical representable pseudofunctor `B(x, -)`. -/
private def coyoneda₀Prelax (x : B) : PrelaxFunctor B Cat.{w, v} :=
  PrelaxFunctor.mkOfHomFunctors (fun y ↦ Cat.of (x ⟶ y))
    (fun a b ↦ postcomposingCat x a b)

/-- Covariant representables preserve left whiskering up to their associator comparison. -/
private theorem coyoneda₀Map₂WhiskerLeft (x : B) :
    ∀ {a b c : B} (h : a ⟶ b) {k l : b ⟶ c} (η : k ⟶ l),
      (coyoneda₀Prelax x).map₂ (h ◁ η) =
        (associatorNatIsoLeftCat x h k).inv ≫
          (coyoneda₀Prelax x).map h ◁ (coyoneda₀Prelax x).map₂ η ≫
          (associatorNatIsoLeftCat x h l).hom := sorry

/-- Covariant representables preserve right whiskering up to their associator comparison. -/
private theorem coyoneda₀Map₂WhiskerRight (x : B) :
    ∀ {a b c : B} {h k : a ⟶ b} (η : h ⟶ k) (l : b ⟶ c),
      (coyoneda₀Prelax x).map₂ (η ▷ l) =
        (associatorNatIsoLeftCat x h l).inv ≫
          (coyoneda₀Prelax x).map₂ η ▷ (coyoneda₀Prelax x).map l ≫
          (associatorNatIsoLeftCat x k l).hom := sorry

/-- Covariant representables carry the ambient associator to the pseudofunctor associativity
coherence assembled from postcomposition associators. -/
private theorem coyoneda₀Map₂Associator (x : B) :
    ∀ {a b c d : B} (h : a ⟶ b) (k : b ⟶ c) (l : c ⟶ d),
      (coyoneda₀Prelax x).map₂ (α_ h k l).hom =
        (associatorNatIsoLeftCat x (h ≫ k) l).inv ≫
          (associatorNatIsoLeftCat x h k).inv ▷ (coyoneda₀Prelax x).map l ≫
          (α_ ((coyoneda₀Prelax x).map h) ((coyoneda₀Prelax x).map k)
            ((coyoneda₀Prelax x).map l)).hom ≫
          (coyoneda₀Prelax x).map h ◁ (associatorNatIsoLeftCat x k l).hom ≫
          (associatorNatIsoLeftCat x h (k ≫ l)).hom := sorry

/-- Left-unitor coherence for the covariant bicategorical representable. -/
private theorem coyoneda₀Map₂LeftUnitor (x : B) :
    ∀ {a b : B} (h : a ⟶ b),
      (coyoneda₀Prelax x).map₂ (λ_ h).hom =
        (associatorNatIsoLeftCat x (𝟙 a) h).inv ≫
          (rightUnitorNatIsoCat x a).hom ▷ (coyoneda₀Prelax x).map h ≫
          (λ_ ((coyoneda₀Prelax x).map h)).hom := sorry

/-- Right-unitor coherence for the covariant bicategorical representable. -/
private theorem coyoneda₀Map₂RightUnitor (x : B) :
    ∀ {a b : B} (h : a ⟶ b),
      (coyoneda₀Prelax x).map₂ (ρ_ h).hom =
        (associatorNatIsoLeftCat x h (𝟙 b)).inv ≫
          (coyoneda₀Prelax x).map h ◁ (rightUnitorNatIsoCat x b).hom ≫
          (ρ_ ((coyoneda₀Prelax x).map h)).hom := sorry

/-- The covariant bicategorical representable pseudofunctor `B(x, -)`.

This is the covariant companion to mathlib's `Bicategory.yoneda₀`: objects are sent to
hom-categories out of `x`, while `1`- and `2`-morphisms act by postcomposition. -/
@[simps!]
def coyoneda₀ (x : B) : B ⥤ᵖ Cat.{w, v} where
  toPrelaxFunctor := coyoneda₀Prelax x
  mapId a := rightUnitorNatIsoCat x a
  mapComp h k := (associatorNatIsoLeftCat x h k).symm
  map₂_whisker_left := coyoneda₀Map₂WhiskerLeft x
  map₂_whisker_right := coyoneda₀Map₂WhiskerRight x
  map₂_associator := coyoneda₀Map₂Associator x
  map₂_left_unitor := coyoneda₀Map₂LeftUnitor x
  map₂_right_unitor := coyoneda₀Map₂RightUnitor x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Precomposition by a `1`-morphism as a strong transformation between covariant
bicategorical representables. -/
@[simps!]
def precomp₂ {a b : B} (f : a ⟶ b) : coyoneda₀ b ⟶ coyoneda₀ a where
  app x := (precomposingCat a b x).obj f
  naturality g := (associatorNatIsoMiddleCat f g).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Precomposition of covariant bicategorical representables, functorial in the
precomposing `1`-morphism. -/
@[simps!]
def precomposing₂ (a b : B) : (a ⟶ b) ⥤ (coyoneda₀ b ⟶ coyoneda₀ a) where
  obj := precomp₂
  map η := { as := { app x := (precomposingCat a b x).map η } }

/-- The prelax core of the covariant bicategorical Yoneda embedding. -/
private def coyonedaPrelax : PrelaxFunctor Bᵒᵖ (B ⥤ᵖ Cat.{w, v}) :=
  PrelaxFunctor.mkOfHomFunctors (fun x ↦ coyoneda₀ x.unop)
    (fun a b ↦ Bicategory.Opposite.unopFunctor a b ⋙ precomposing₂ b.unop a.unop)

/-- Naturality of the objectwise left-unitor comparison for the covariant Yoneda embedding. -/
private theorem coyonedaMapIdNaturality (a : Bᵒᵖ) :
    ∀ {b c : B} (f : b ⟶ c),
      (coyonedaPrelax.obj a).map f ◁ (leftUnitorNatIsoCat a.unop c).hom ≫
          ((Pseudofunctor.StrongTrans.id (coyonedaPrelax.obj a)).naturality f).hom =
        ((coyonedaPrelax.map (𝟙 a)).naturality f).hom ≫
          (leftUnitorNatIsoCat a.unop b).hom ▷ (coyonedaPrelax.obj a).map f := sorry

/-- The identity comparison for the covariant bicategorical Yoneda embedding. -/
private def coyonedaMapId (a : Bᵒᵖ) :
    coyonedaPrelax.map (𝟙 a) ≅ 𝟙 (coyonedaPrelax.obj a) :=
  Pseudofunctor.StrongTrans.isoMk (fun b ↦ leftUnitorNatIsoCat a.unop b)
    (coyonedaMapIdNaturality a)

/-- Naturality of the objectwise associator comparison for the covariant Yoneda embedding. -/
private theorem coyonedaMapCompNaturality {a b c : Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    ∀ {x y : B} (h : x ⟶ y),
      (coyonedaPrelax.obj a).map h ◁ (associatorNatIsoRightCat g.unop f.unop y).hom ≫
          ((coyonedaPrelax.map f ≫ coyonedaPrelax.map g).naturality h).hom =
        ((coyonedaPrelax.map (f ≫ g)).naturality h).hom ≫
          (associatorNatIsoRightCat g.unop f.unop x).hom ▷ (coyonedaPrelax.obj c).map h := sorry

/-- The composition comparison for the covariant bicategorical Yoneda embedding. -/
private def coyonedaMapComp {a b c : Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    coyonedaPrelax.map (f ≫ g) ≅ coyonedaPrelax.map f ≫ coyonedaPrelax.map g :=
  Pseudofunctor.StrongTrans.isoMk
    (fun x ↦ associatorNatIsoRightCat g.unop f.unop x)
    (coyonedaMapCompNaturality f g)

/-- The covariant bicategorical Yoneda embedding preserves left whiskering. -/
private theorem coyonedaMap₂WhiskerLeft :
    ∀ {a b c : Bᵒᵖ} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      coyonedaPrelax.map₂ (f ◁ η) =
        (coyonedaMapComp f g).hom ≫
          coyonedaPrelax.map f ◁ coyonedaPrelax.map₂ η ≫
          (coyonedaMapComp f h).inv := sorry

/-- The covariant bicategorical Yoneda embedding preserves right whiskering. -/
private theorem coyonedaMap₂WhiskerRight :
    ∀ {a b c : Bᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      coyonedaPrelax.map₂ (η ▷ h) =
        (coyonedaMapComp f h).hom ≫
          coyonedaPrelax.map₂ η ▷ coyonedaPrelax.map h ≫
          (coyonedaMapComp g h).inv := sorry

/-- The covariant bicategorical Yoneda embedding preserves the associator coherence. -/
private theorem coyonedaMap₂Associator :
    ∀ {a b c d : Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      coyonedaPrelax.map₂ (α_ f g h).hom =
        (coyonedaMapComp (f ≫ g) h).hom ≫
          (coyonedaMapComp f g).hom ▷ coyonedaPrelax.map h ≫
          (α_ (coyonedaPrelax.map f) (coyonedaPrelax.map g)
            (coyonedaPrelax.map h)).hom ≫
          coyonedaPrelax.map f ◁ (coyonedaMapComp g h).inv ≫
          (coyonedaMapComp f (g ≫ h)).inv := sorry

/-- The covariant bicategorical Yoneda embedding preserves left-unit coherence. -/
private theorem coyonedaMap₂LeftUnitor :
    ∀ {a b : Bᵒᵖ} (f : a ⟶ b),
      coyonedaPrelax.map₂ (λ_ f).hom =
        (coyonedaMapComp (𝟙 a) f).hom ≫
          (coyonedaMapId a).hom ▷ coyonedaPrelax.map f ≫
          (λ_ (coyonedaPrelax.map f)).hom := sorry

/-- The covariant bicategorical Yoneda embedding preserves right-unit coherence. -/
private theorem coyonedaMap₂RightUnitor :
    ∀ {a b : Bᵒᵖ} (f : a ⟶ b),
      coyonedaPrelax.map₂ (ρ_ f).hom =
        (coyonedaMapComp f (𝟙 b)).hom ≫
          coyonedaPrelax.map f ◁ (coyonedaMapId b).hom ≫
          (ρ_ (coyonedaPrelax.map f)).hom := sorry

variable (B : Type u) [Bicategory.{w, v} B] in
/-- The covariant bicategorical Yoneda embedding.

It sends `x : Bᵒᵖ` to `B(x.unop, -)`, and sends a `1`-morphism by precomposition. -/
@[simps!]
def coyoneda : Bᵒᵖ ⥤ᵖ B ⥤ᵖ Cat.{w, v} where
  toPrelaxFunctor := coyonedaPrelax
  mapId := coyonedaMapId
  mapComp := coyonedaMapComp
  map₂_whisker_left := coyonedaMap₂WhiskerLeft
  map₂_whisker_right := coyonedaMap₂WhiskerRight
  map₂_associator := coyonedaMap₂Associator
  map₂_left_unitor := coyonedaMap₂LeftUnitor
  map₂_right_unitor := coyonedaMap₂RightUnitor

/- Data and axiom audit (mathlib 4.32):

The object, `1`-morphism, and `2`-morphism actions of `coyoneda₀`, `precomp₂`, and
`coyoneda` are explicit postcomposition and precomposition data. Any `sorryAx` dependency is
confined to pseudofunctor coherence laws and inherited bicategorical coherence. -/

end CategoryTheory.Bicategory
