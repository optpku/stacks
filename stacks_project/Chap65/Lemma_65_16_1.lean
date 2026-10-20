module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation.ChangeOfBase

/-!
# Lemma 65.16.1

Change of base for sheaves, representables, algebraic spaces, and presentations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 65.16.1. Extension along a base morphism has the coproduct section formula;
restriction evaluates on the same test scheme over the original base. Both preserve
representables, algebraic spaces, and their presentations. -/
@[stacks 03I4] #check (AlgebraicGeometry.AlgebraicSpace.extendBasePresheaf_obj :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (F : (Over S)ᵒᵖ ⥤ Type u) (T' : Over S'),
    (extendBasePresheaf g F).obj (op T') =
      Σ φ : T' ⟶ Over.mk g, F.obj (op (Over.mk φ.left)))

#check (AlgebraicGeometry.AlgebraicSpace.extendBasePresheafYonedaIso :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X : Over S),
    extendBasePresheaf g (yoneda.obj X) ≅ yoneda.obj ((Over.map g).obj X))

#check (AlgebraicGeometry.AlgebraicSpace.extendBase_spec :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S),
    Presheaf.IsSheaf (Scheme.fppfTopology.over S')
        (extendBasePresheaf g F.functorOfPoints) ∧
      yoneda.relativelyRepresentable (Limits.diag (extendBasePresheaf g F.functorOfPoints)) ∧
        ∃ (U : Over S') (atlas : yoneda.obj U ⟶ extendBasePresheaf g F.functorOfPoints),
          (MorphismProperty.over (@Etale)).presheaf atlas ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S') atlas)

#check (AlgebraicGeometry.AlgebraicSpace.baseChangePresheaf_obj :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (F' : (Over S')ᵒᵖ ⥤ Type u) (T : Over S),
    (baseChangePresheaf g F').obj (op T) = F'.obj (op ((Over.map g).obj T)))

#check (AlgebraicGeometry.AlgebraicSpace.baseChangePresheafYonedaIso :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : Over S'),
    baseChangePresheaf g (yoneda.obj X') ≅ yoneda.obj ((Over.pullback g).obj X'))

#check (AlgebraicGeometry.AlgebraicSpace.baseChange_spec :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (F' : AlgebraicSpace S'),
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
        (baseChangePresheaf g F'.functorOfPoints) ∧
      yoneda.relativelyRepresentable (Limits.diag (baseChangePresheaf g F'.functorOfPoints)) ∧
        ∃ (U : Over S) (atlas : yoneda.obj U ⟶ baseChangePresheaf g F'.functorOfPoints),
          (MorphismProperty.over (@Etale)).presheaf atlas ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas)

#check (AlgebraicGeometry.AlgebraicSpace.Presentation.extendBase :
  ∀ {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S'),
    Presentation F → Presentation (AlgebraicSpace.extendBase g F))

#check (AlgebraicGeometry.AlgebraicSpace.Presentation.baseChange :
  ∀ {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S'),
    Presentation F' → Presentation (AlgebraicSpace.baseChange g F'))

end AlgebraicGeometry.AlgebraicSpace
