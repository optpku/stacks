module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion

/-!
# Morphism action of set-valued completion

The set-valued completion of a natural transformation is induced by `limMap` of left
whiskering with each truncation tower. Completion preserves pullbacks, yielding a
canonical comparison from the completion of a pullback to the pullback of the
completions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The limit maps induced by a natural transformation commute with the maps of
completed functors induced by complete local algebra morphisms. -/
private theorem typesCompletionMap_naturality
    {F G : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G)
    {S T : CompleteLocalAlgCat Λ k} (h : S ⟶ T) :
    (typesCompletion F).map h ≫ limMap (whiskerLeft T.truncationSystem α) =
      limMap (whiskerLeft S.truncationSystem α) ≫ (typesCompletion G).map h := sorry

/-- The set-valued completion of a natural transformation `α : F ⟶ G`, with component at
a complete local algebra `S` given by `limMap` of `α` whiskered by the truncation tower of
`S`. -/
def typesCompletionMap {F G : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G) :
    typesCompletion F ⟶ typesCompletion G where
  app S := limMap (whiskerLeft S.truncationSystem α)
  naturality {_ _} h := private typesCompletionMap_naturality α h

/-- The component of `typesCompletionMap α` at `S` is `limMap` of the left whiskering of
`α` by the truncation tower of `S`. -/
theorem typesCompletionMap_app {F G : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G)
    (S : CompleteLocalAlgCat Λ k) :
    (typesCompletionMap α).app S = limMap (whiskerLeft S.truncationSystem α) := sorry

/-- Set-valued completion preserves identity natural transformations. -/
theorem typesCompletionMap_id (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    typesCompletionMap (𝟙 F) = 𝟙 (typesCompletion F) := sorry

/-- Set-valued completion preserves composition of natural transformations. -/
theorem typesCompletionMap_comp {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (α : F ⟶ G) (β : G ⟶ H) :
    typesCompletionMap (α ≫ β) = typesCompletionMap α ≫ typesCompletionMap β := sorry

/-- The component at a complete local algebra `S` of the comparison identifying the
completion of a pullback with the pullback of the completions. -/
def typesCompletionPullbackIsoApp {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    (typesCompletion (pullback f g)).obj S ≅
      (pullback (typesCompletionMap f) (typesCompletionMap g)).obj S :=
  HasLimit.isoOfNatIso
      (PreservesPullback.iso
        ((whiskeringLeft ℕᵒᵖ (ArtinianLocalAlgCat Λ k) (Type w)).obj S.truncationSystem) f g) ≪≫
    PreservesPullback.iso (lim : (ℕᵒᵖ ⥤ Type w) ⥤ Type w)
      (whiskerLeft S.truncationSystem f) (whiskerLeft S.truncationSystem g) ≪≫
    (PreservesPullback.iso ((evaluation (CompleteLocalAlgCat Λ k) (Type w)).obj S)
      (typesCompletionMap f) (typesCompletionMap g)).symm

/-- The hom-component of `typesCompletionPullbackIsoApp` is the composite of the
whiskering, limit, and evaluation pullback-preservation isomorphisms. -/
theorem typesCompletionPullbackIsoApp_hom {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    (typesCompletionPullbackIsoApp f g S).hom =
      (HasLimit.isoOfNatIso
          (PreservesPullback.iso
            ((whiskeringLeft ℕᵒᵖ (ArtinianLocalAlgCat Λ k) (Type w)).obj
              S.truncationSystem) f g)).hom ≫
        (PreservesPullback.iso (lim : (ℕᵒᵖ ⥤ Type w) ⥤ Type w)
          (whiskerLeft S.truncationSystem f) (whiskerLeft S.truncationSystem g)).hom ≫
        (PreservesPullback.iso ((evaluation (CompleteLocalAlgCat Λ k) (Type w)).obj S)
          (typesCompletionMap f) (typesCompletionMap g)).inv := sorry

/-- Naturality of the componentwise pullback-preservation comparison for set-valued
completion. -/
theorem typesCompletionPullbackIso_naturality {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) {S T : CompleteLocalAlgCat Λ k} (h : S ⟶ T) :
    (typesCompletion (pullback f g)).map h ≫ (typesCompletionPullbackIsoApp f g T).hom =
      (typesCompletionPullbackIsoApp f g S).hom ≫
        (pullback (typesCompletionMap f) (typesCompletionMap g)).map h := sorry

/-- The canonical isomorphism `typesCompletion (pullback f g) ≅ pullback (typesCompletionMap f)
(typesCompletionMap g)` coming from preservation of limits by whiskering and by `lim`. -/
def typesCompletionPullbackIso {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) :
    typesCompletion (pullback f g) ≅ pullback (typesCompletionMap f) (typesCompletionMap g) :=
  NatIso.ofComponents (fun S ↦ typesCompletionPullbackIsoApp f g S)
    (typesCompletionPullbackIso_naturality f g)

/-- The hom-component of `typesCompletionPullbackIso` at `S` is
`typesCompletionPullbackIsoApp`. -/
theorem typesCompletionPullbackIso_hom {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    (typesCompletionPullbackIso f g).hom.app S =
      (typesCompletionPullbackIsoApp f g S).hom := sorry

end CategoryTheory.Functor
