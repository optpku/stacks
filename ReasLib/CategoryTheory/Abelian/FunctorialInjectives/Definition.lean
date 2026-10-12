/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.NatTrans.Arrow

@[expose] public section

/-!
# Functorial Injectives

The primary data are an endofunctor and a natural monomorphism from the identity.  The associated
functor to the arrow category is derived API, so consumers do not have to transport along an
equality asserting that its source is the identity.
-/

namespace CategoryTheory

universe v u

/-- A category has functorial injective embeddings if it is equipped with an endofunctor `I`, a
natural transformation `𝟭 C ⟶ I` whose components are monomorphisms, and a choice of injective
object `I.obj A` for every `A`. -/
@[stacks 0139]
class HasFunctorialInjectives (C : Type u) [Category.{v} C] where
  /-- The functor of chosen injective targets. -/
  functor : C ⥤ C
  /-- The natural family of chosen injective embeddings. -/
  ι : 𝟭 C ⟶ functor
  /-- Each chosen embedding is a monomorphism. -/
  mono_app (A : C) : Mono (ι.app A)
  /-- Each chosen target is injective. -/
  injective_obj (A : C) : Injective (functor.obj A)

attribute [instance] HasFunctorialInjectives.mono_app
attribute [instance] HasFunctorialInjectives.injective_obj

namespace HasFunctorialInjectives

section

variable {C : Type u} [Category.{v} C] [HasFunctorialInjectives C]

/-- The chosen natural embedding into injective targets is a monomorphism. -/
@[stacks 0139 "natural injective embedding is monomorphic"]
instance mono_ι : Mono (HasFunctorialInjectives.ι (C := C)) := sorry

/-- The chosen injective object associated to `A`. -/
@[stacks 0139 "chosen functorial injective target"]
abbrev obj (A : C) : C := functor.obj A

/-- The map between chosen injective targets induced by a morphism. -/
@[stacks 0139 "map between functorial injective targets"]
abbrev map {A B : C} (f : A ⟶ B) : obj A ⟶ obj B := functor.map f

/-- The components of the chosen embeddings, regarded as a functor to the arrow category. -/
@[stacks 0139 "functor of chosen injective embeddings"]
noncomputable def arrowFunctor : C ⥤ Arrow C :=
  (HasFunctorialInjectives.ι (C := C)).arrowFunctor

/-- The source functor of the derived arrow functor is the identity. -/
@[simp, stacks 0139 "source of the injective-embedding arrow functor"]
theorem arrowFunctor.comp.left : arrowFunctor ⋙ Arrow.leftFunc = 𝟭 C := sorry

/-- The source of the chosen arrow `arrowFunctor.obj A` is `A`. -/
@[simp, stacks 0139 "source of a chosen injective-embedding arrow"]
theorem arrowFunctor.obj.left (A : C) : (arrowFunctor.obj A).left = A := sorry

/-- The target of the chosen arrow `arrowFunctor.obj A` is the chosen injective object under
`A`. -/
@[simp, stacks 0139 "target of a chosen injective-embedding arrow"]
theorem arrowFunctor.obj.right (A : C) : (arrowFunctor.obj A).right = obj A := sorry

/-- The morphism of `arrowFunctor.obj A` is the chosen embedding of `A`. -/
@[simp, stacks 0139 "morphism of a chosen injective-embedding arrow"]
theorem arrowFunctor.obj.hom (A : C) :
    (arrowFunctor.obj A).hom = HasFunctorialInjectives.ι.app A := sorry

/-- The right-hand map of the square `arrowFunctor.map f` is the functorially induced target
map. -/
@[simp, stacks 0139 "target map of the injective-embedding arrow functor"]
theorem arrowFunctor.map.right {A B : C} (f : A ⟶ B) :
    (arrowFunctor.map f).right = map f := sorry

/-- The canonical injective presentation determined by the chosen functorial injective embedding
of `A`. -/
@[stacks 0139 "canonical functorial injective presentation"]
def presentation (A : C) : InjectivePresentation A where
  J := obj A
  injective := injective_obj A
  f := HasFunctorialInjectives.ι.app A
  mono := mono_app A

/-- The chosen embeddings and functorially induced target maps form a commutative square. -/
@[stacks 0139 "naturality square of chosen injective embeddings"]
theorem ι.commSq {A B : C} (f : A ⟶ B) :
    CommSq f (HasFunctorialInjectives.ι.app A)
      (HasFunctorialInjectives.ι.app B) (map f) := sorry

/-- Equality form of `HasFunctorialInjectives.ι.commSq`. -/
@[reassoc (attr := simp), stacks 0139 "naturality of chosen injective embeddings"]
theorem ι.naturality {A B : C} (f : A ⟶ B) :
    f ≫ HasFunctorialInjectives.ι.app B =
      HasFunctorialInjectives.ι.app A ≫ map f := sorry

end

section ArrowCompatibility

variable {C : Type u} [Category.{v} C]

/-- The objectwise source identification supplied by an arrow functor whose source functor is the
identity. -/
@[stacks 0139 "source object of a compatible arrow functor"]
theorem sourceObj_eq (J : C ⥤ Arrow C) (hJ : J ⋙ Arrow.leftFunc = 𝟭 C) (A : C) :
    (J.obj A).left = A := sorry

/-- Compatibility constructor from the former arrow-functor presentation of functorial injective
embeddings. New constructions should provide `functor` and `ι` directly. -/
@[reducible, stacks 0139 "compatibility constructor from an arrow functor"]
noncomputable def ofArrowFunctor
    (J : C ⥤ Arrow C) (hJ : J ⋙ Arrow.leftFunc = 𝟭 C)
    (mono_app : ∀ A, Mono ((J.obj A).hom))
    (injective_obj : ∀ A, Injective ((J.obj A).right)) :
    HasFunctorialInjectives C where
  functor := J ⋙ Arrow.rightFunc
  ι :=
    { app := fun A =>
        eqToHom (congrArg (fun F : C ⥤ C => F.obj A) hJ).symm ≫ (J.obj A).hom
      naturality := fun _ _ _ => sorry }
  mono_app := fun _ => sorry
  injective_obj := injective_obj

end ArrowCompatibility

end HasFunctorialInjectives

/-- Functorial injective embeddings provide enough injectives. -/
instance {C : Type u} [Category.{v} C] [HasFunctorialInjectives C] :
    EnoughInjectives C where
  presentation A := ⟨HasFunctorialInjectives.presentation A⟩



end CategoryTheory
