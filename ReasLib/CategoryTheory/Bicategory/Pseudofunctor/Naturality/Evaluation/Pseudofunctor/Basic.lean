/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.Action.Basic

/-!
# Curried bicategorical evaluation

The pseudofunctor sending a source object to point evaluation, with its unit,
composition, and coherence data. Computation rules live in
`Evaluation.Pseudofunctor.Computations`.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Evaluation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Naturality of the pointwise unit comparison for curried evaluation. -/
private theorem evaluationMapId_naturality
    (a : B) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    η.app a ◁ (G.mapId a).hom ≫
        ((StrongTrans.id
          ((evaluationAt D a).toPseudofunctor)).naturality η).hom =
      ((evaluationMap D (𝟙 a)).naturality η).hom ≫
        (F.mapId a).hom ▷ η.app a := sorry

variable (D) in
/-- The unit comparison for curried evaluation, obtained pointwise from the unit
comparisons of the pseudofunctors being evaluated. -/
def evaluationMapId (a : B) :
    evaluationMap D (𝟙 a) ≅
      𝟙 ((evaluationAt D a).toPseudofunctor) :=
  StrongTrans.isoMk (fun F => F.mapId a) (evaluationMapId_naturality a)

/-- Naturality of the pointwise composition comparison for curried evaluation. -/
private theorem evaluationMapComp_naturality
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    {F G : Pseudofunctor B D} (η : F ⟶ G) :
    η.app a ◁ (G.mapComp f g).hom ≫
        ((evaluationMap D f ≫ evaluationMap D g).naturality η).hom =
      ((evaluationMap D (f ≫ g)).naturality η).hom ≫
        (F.mapComp f g).hom ▷ η.app c := sorry

variable (D) in
/-- The composition comparison for curried evaluation, obtained pointwise from the
composition comparisons of the pseudofunctors being evaluated. -/
def evaluationMapComp
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    evaluationMap D (f ≫ g) ≅
      evaluationMap D f ≫ evaluationMap D g :=
  StrongTrans.isoMk (fun F => F.mapComp f g)
    (evaluationMapComp_naturality f g)

/-- Curried evaluation is compatible with left whiskering of source `2`-morphisms. -/
private theorem evaluationMap₂_whisker_left
    {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    evaluationMap₂ D (f ◁ η) =
      (evaluationMapComp D f g).hom ≫
        evaluationMap D f ◁ evaluationMap₂ D η ≫
        (evaluationMapComp D f h).inv := sorry

/-- Curried evaluation is compatible with right whiskering of source `2`-morphisms. -/
private theorem evaluationMap₂_whisker_right
    {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    evaluationMap₂ D (η ▷ h) =
      (evaluationMapComp D f h).hom ≫
        evaluationMap₂ D η ▷ evaluationMap D h ≫
        (evaluationMapComp D g h).inv := sorry

/-- Curried evaluation is compatible with the left unitor of the source bicategory. -/
private theorem evaluationMap₂_left_unitor
    {a b : B} (f : a ⟶ b) :
    evaluationMap₂ D (λ_ f).hom =
      (evaluationMapComp D (𝟙 a) f).hom ≫
        (evaluationMapId D a).hom ▷ evaluationMap D f ≫
        (λ_ (evaluationMap D f)).hom := sorry

/-- Curried evaluation is compatible with the right unitor of the source bicategory. -/
private theorem evaluationMap₂_right_unitor
    {a b : B} (f : a ⟶ b) :
    evaluationMap₂ D (ρ_ f).hom =
      (evaluationMapComp D f (𝟙 b)).hom ≫
        evaluationMap D f ◁ (evaluationMapId D b).hom ≫
        (ρ_ (evaluationMap D f)).hom := sorry

/-- Curried evaluation is compatible with the associator of the source bicategory. -/
private theorem evaluationMap₂_associator
    {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    evaluationMap₂ D (α_ f g h).hom =
      (evaluationMapComp D (f ≫ g) h).hom ≫
        (evaluationMapComp D f g).hom ▷
          evaluationMap D h ≫
        (α_ (evaluationMap D f) (evaluationMap D g)
          (evaluationMap D h)).hom ≫
        evaluationMap D f ◁
          (evaluationMapComp D g h).inv ≫
        (evaluationMapComp D f (g ≫ h)).inv := sorry

/-- Bicategorical evaluation, curried in the source object. It is the pseudofunctor analogue
of `CategoryTheory.evaluation`: an object `a` is sent to evaluation at `a`, a `1`-morphism
is sent to the corresponding evaluation strong transformation, and a `2`-morphism is sent
to the corresponding modification. -/
def evaluation
    (B : Type uB) [Bicategory.{wB, vB} B]
    (D : Type uD) [Bicategory.{wD, vD} D] :
    Pseudofunctor B (Pseudofunctor (Pseudofunctor B D) D) where
  toPrelaxFunctor :=
    PrelaxFunctor.mkOfHomFunctors
      (fun a => (evaluationAt D a).toPseudofunctor)
      (evaluationMapFunctor D)
  mapId := evaluationMapId D
  mapComp := evaluationMapComp D
  map₂_whisker_left := evaluationMap₂_whisker_left (D := D)
  map₂_whisker_right := evaluationMap₂_whisker_right (D := D)
  map₂_left_unitor := evaluationMap₂_left_unitor (D := D)
  map₂_right_unitor := evaluationMap₂_right_unitor (D := D)
  map₂_associator := evaluationMap₂_associator (D := D)

end Evaluation

end Pseudofunctor

end CategoryTheory
