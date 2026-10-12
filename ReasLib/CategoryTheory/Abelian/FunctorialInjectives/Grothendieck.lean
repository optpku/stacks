/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition

@[expose] public section

namespace CategoryTheory

universe w v u

namespace IsGrothendieckAbelian

open MorphismProperty
open ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The functor sending an object to its zero morphism into the zero object. -/
noncomputable def zeroArrowFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (0 : X ⟶ (0 : C))
  map {X Y} f := Arrow.homMk f (0 : (0 : C) ⟶ (0 : C)) sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The canonical injective-presentation arrow in a Grothendieck abelian category, obtained by
functorially factoring the zero map. -/
@[stacks 079H "injective-presentation arrow"]
noncomputable def injectiveArrow (X : C) : Arrow C :=
  Arrow.mk (IsGrothendieckAbelian.monoMapFactorizationDataRlp (0 : X ⟶ (0 : C))).i

/-- The functorial factorization datum underlying the chosen Grothendieck injective embeddings. -/
noncomputable abbrev injectiveFactorization :=
  functorialFactorizationData (monomorphisms C) (monomorphisms C).rlp

/-- The map between canonical Grothendieck injective-presentation arrows induced by a morphism. -/
noncomputable def injectiveArrowMap {X Y : C} (f : X ⟶ Y) :
    injectiveArrow X ⟶ injectiveArrow Y :=
  Arrow.homMk f
    ((injectiveFactorization (C := C)).mapZ (zeroArrowFunctor.map f)) sorry

/-- The endofunctor of injective targets supplied by functorial factorization in a Grothendieck
abelian category. -/
@[stacks 079H "injective-target functor"]
noncomputable def injectiveFunctor : C ⥤ C where
  obj X := (injectiveArrow X).right
  map f := (injectiveArrowMap f).right
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The natural monomorphism into the functorial injective target in a Grothendieck abelian
category. -/
@[stacks 079H "functorial injective embedding"]
noncomputable def injectiveι : 𝟭 C ⟶ injectiveFunctor where
  app X := (injectiveArrow X).hom
  naturality _ _ _ := sorry

/-- The named natural embedding into Grothendieck injective targets is monomorphic. -/
@[stacks 079H "functorial injective embedding is monomorphic", instance]
theorem mono_injectiveι : Mono (injectiveι (C := C)) := sorry

/-- Every object selected by the named Grothendieck injective-target functor is injective. -/
@[stacks 079H "functorial injective targets are injective", instance]
theorem injectiveFunctor.obj_injective (X : C) :
    Injective ((injectiveFunctor (C := C)).obj X) := sorry

/-- A Grothendieck abelian category has a canonical fallback choice of functorial injective
embeddings. The low priority leaves room for a more specific choice on a concrete category. -/
@[stacks 079H "Grothendieck functorial injective embeddings", reducible]
noncomputable instance (priority := 100) hasFunctorialInjectives :
    HasFunctorialInjectives C where
  functor := injectiveFunctor
  ι := injectiveι
  mono_app _ := sorry
  injective_obj _ := sorry

end IsGrothendieckAbelian



end CategoryTheory
