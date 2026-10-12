/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.NatTrans.Arrow

@[expose] public section

/-!
# Functorial Projective Surjections

The primary data are an endofunctor and a natural epimorphism to the identity.  The associated
functor to the arrow category is derived API.  This is dual to
`ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition`.
-/

namespace CategoryTheory

universe v u

/-- Definition 12.28.5: a category has functorial projective surjections if it is equipped with an
endofunctor `P`, a natural transformation `P ⟶ 𝟭 C` whose components are epimorphisms, and a
choice of projective object `P.obj A` for every `A`. -/
@[stacks 013F]
class HasFunctorialProjectiveSurjections (C : Type u) [Category.{v} C] where
  /-- The functor of chosen projective sources. -/
  overFunctor : C ⥤ C
  /-- The natural family of chosen projective surjections. -/
  πNatTrans : overFunctor ⟶ 𝟭 C
  /-- Each chosen surjection is an epimorphism. -/
  epi_obj (A : C) : Epi (πNatTrans.app A)
  /-- Each chosen source is projective. -/
  projective_obj (A : C) : Projective (overFunctor.obj A)

attribute [instance] HasFunctorialProjectiveSurjections.epi_obj
attribute [instance] HasFunctorialProjectiveSurjections.projective_obj

namespace HasFunctorialProjectiveSurjections

section

variable {C : Type u} [Category.{v} C] [HasFunctorialProjectiveSurjections C]

/-- The chosen projective object over `A`. -/
abbrev over (A : C) : C := overFunctor.obj A

/-- The chosen functorial projective surjection onto `A`. -/
abbrev π (A : C) : over A ⟶ A := πNatTrans.app A

/-- The map between chosen projective sources induced by a morphism. -/
abbrev overMap {A B : C} (f : A ⟶ B) : over A ⟶ over B := overFunctor.map f

/-- The components of the chosen surjections, regarded as a functor to the arrow category. -/
@[stacks 013F "functor of chosen projective surjections"]
noncomputable def arrowFunctor : C ⥤ Arrow C := πNatTrans.arrowFunctor

/-- The target functor of the derived arrow functor is the identity. -/
@[simp, stacks 013F "target of the projective-surjection arrow functor"]
theorem arrowFunctor.comp.right : arrowFunctor ⋙ Arrow.rightFunc = 𝟭 C := sorry

/-- The target of the chosen arrow `arrowFunctor.obj A` is `A`. -/
@[simp, stacks 013F "target of a chosen projective-surjection arrow"]
theorem arrowFunctor.obj.right (A : C) : (arrowFunctor.obj A).right = A := sorry

/-- The source of the chosen arrow `arrowFunctor.obj A` is the chosen projective object over
`A`. -/
@[simp, stacks 013F "source of a chosen projective-surjection arrow"]
theorem arrowFunctor.obj.left (A : C) : (arrowFunctor.obj A).left = over A := sorry

/-- The morphism of `arrowFunctor.obj A` is the chosen surjection onto `A`. -/
@[simp, stacks 013F "morphism of a chosen projective-surjection arrow"]
theorem arrowFunctor.obj.hom (A : C) : (arrowFunctor.obj A).hom = π A := sorry

/-- The left-hand map of the square `arrowFunctor.map f` is the functorially induced source
map. -/
@[simp, stacks 013F "source map of the projective-surjection arrow functor"]
theorem arrowFunctor.map.left {A B : C} (f : A ⟶ B) :
    (arrowFunctor.map f).left = overMap f := sorry

/-- The canonical projective presentation determined by the chosen functorial surjection onto
`A`. -/
@[stacks 013F "canonical functorial projective presentation"]
def presentation (A : C) : ProjectivePresentation A where
  p := over A
  projective := projective_obj A
  f := π A
  epi := epi_obj A

/-- The chosen projective surjections commute with the functorially induced source maps. -/
@[reassoc (attr := simp), stacks 013F "naturality of chosen projective surjections"]
theorem π.naturality {A B : C} (f : A ⟶ B) : overMap f ≫ π B = π A ≫ f := sorry

/-- Named access to the projectivity instance on a chosen source. -/
abbrev over_projective (A : C) : Projective (over A) := projective_obj A

/-- Named access to the epimorphism instance on a chosen surjection. -/
abbrev π_epi (A : C) : Epi (π A) := epi_obj A

/-- Functorial projective surjections provide enough projectives. -/
instance : EnoughProjectives C where
  presentation A := ⟨HasFunctorialProjectiveSurjections.presentation A⟩

end

section ArrowCompatibility

variable {C : Type u} [Category.{v} C]

/-- The objectwise target identification supplied by an arrow functor whose target functor is the
identity. -/
theorem targetObj_eq (P : C ⥤ Arrow C) (hP : P ⋙ Arrow.rightFunc = 𝟭 C) (A : C) :
    (P.obj A).right = A := sorry

/-- Compatibility constructor from the former arrow-functor presentation of functorial projective
surjections.  New constructions should provide `overFunctor` and `πNatTrans` directly. -/
@[reducible]
noncomputable def ofArrowFunctor
    (P : C ⥤ Arrow C) (hP : P ⋙ Arrow.rightFunc = 𝟭 C)
    (epi_obj : ∀ A, Epi ((P.obj A).hom))
    (projective_obj : ∀ A, Projective ((P.obj A).left)) :
    HasFunctorialProjectiveSurjections C where
  overFunctor := P ⋙ Arrow.leftFunc
  πNatTrans :=
    { app := fun A =>
        (P.obj A).hom ≫ eqToHom (congrArg (fun F : C ⥤ C => F.obj A) hP)
      naturality := fun _ _ _ => sorry }
  epi_obj := fun _ => sorry
  projective_obj := projective_obj

end ArrowCompatibility

end HasFunctorialProjectiveSurjections

end CategoryTheory
