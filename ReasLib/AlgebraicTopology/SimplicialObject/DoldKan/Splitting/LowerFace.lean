module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting.Decomposition

/-!
@stack 017U

# The canonical lower-face Dold--Kan splitting

This file packages the lower-face decomposition as a monic splitting and records its functorial
map and the resulting functor from simplicial objects to split simplicial objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace normalizedMoore.lowerFace

namespace cofan

/-- The explicit inverse of the lower-face decomposition gives the descent map for a cofan. -/
@[stacks 017U "lower-face splitting explicit cofan descent"]
theorem desc_fac (U : SimplicialObject A) (Δ : SimplexCategoryᵒᵖ)
    (s : Cocone (Discrete.functor (normalizedMoore.lowerFace.summand U Δ)))
    (a : Discrete (Splitting.IndexSet Δ)) :
    (normalizedMoore.lowerFace.cofan U Δ).ι.app a ≫
        (normalizedMoore.lowerFace.decomposition.iso U Δ).inv ≫
          Sigma.desc (fun b ↦ s.ι.app ⟨b⟩) = s.ι.app a := sorry

/-- The explicit lower-face descent is unique among maps with the prescribed coproduct legs. -/
@[stacks 017U "lower-face splitting explicit cofan descent uniqueness"]
theorem desc_uniq (U : SimplicialObject A) (Δ : SimplexCategoryᵒᵖ)
    (s : Cocone (Discrete.functor (normalizedMoore.lowerFace.summand U Δ)))
    (m : U.obj Δ ⟶ s.pt)
    (hm : ∀ a : Discrete (Splitting.IndexSet Δ),
      (normalizedMoore.lowerFace.cofan U Δ).ι.app a ≫ m = s.ι.app a) :
    m = (normalizedMoore.lowerFace.decomposition.iso U Δ).inv ≫
      Sigma.desc (fun b ↦ s.ι.app ⟨b⟩) := sorry

/-- The lower-face cofan is a colimit, equivalently the lower-face summands form a splitting in
each simplicial degree. -/
@[stacks 017U "lower-face splitting universal property",
  stacks 017V "lower-face splitting universal property"]
noncomputable def isColimit (U : SimplicialObject A) (Δ : SimplexCategoryᵒᵖ) :
    IsColimit (normalizedMoore.lowerFace.cofan U Δ) :=
  { desc := fun s ↦
      (normalizedMoore.lowerFace.decomposition.iso U Δ).inv ≫
        Sigma.desc (fun b ↦ s.ι.app ⟨b⟩)
    fac := fun s a ↦ desc_fac U Δ s a
    uniq := fun s m hm ↦ desc_uniq U Δ s m hm }

end cofan

/-- The canonical splitting whose distinguished degree-`n` object is the intersection of the
kernels of the lower faces. -/
@[stacks 017U "canonical lower-face splitting",
  stacks 017V "canonical lower-face splitting"]
noncomputable def splitting (U : SimplicialObject A) : Splitting U where
  N n := (subobject U n : A)
  ι n := (subobject U n).arrow
  isColimit' Δ := cofan.isColimit U Δ

namespace splitting

/-- The distinguished inclusions in the canonical lower-face splitting are monomorphisms. -/
@[stacks 017U "monicity of the lower-face splitting",
  stacks 017V "monicity of the lower-face splitting"]
instance isMonic (U : SimplicialObject A) : (splitting U).IsMonic := sorry

/-- The canonical lower-face splitting witnesses that every simplicial object in an abelian
category is split. -/
@[stacks 017U "splitness from the lower-face splitting",
  stacks 017V "splitness from the lower-face splitting"]
theorem isSplit (U : SimplicialObject A) : SimplicialObject.IsSplit U := sorry

/-- The distinguished object of the lower-face splitting is the lower-face normalized Moore
subobject. -/
@[simp, stacks 017U "lower-face splitting distinguished object",
  stacks 017V "lower-face splitting distinguished object"]
theorem summand (U : SimplicialObject A) (n : ℕ) :
    (splitting U).N n = (subobject U n : A) := sorry

/-- The distinguished inclusion of the lower-face splitting is the subobject inclusion. -/
@[simp, stacks 017U "lower-face splitting distinguished inclusion",
  stacks 017V "lower-face splitting distinguished inclusion"]
theorem inclusion (U : SimplicialObject A) (n : ℕ) :
    (splitting U).ι n = (subobject U n).arrow := sorry

/-- The canonical projection from degree-`n` simplices onto the lower-face normalized summand. -/
@[stacks 017U "lower-face normalized summand projection",
  stacks 017V "lower-face normalized summand projection"]
noncomputable def projection (U : SimplicialObject A) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶ (subobject U n : A) :=
  (splitting U).πSummand (Splitting.IndexSet.id (op ⦋n⦌))

/-- The normalized-summand inclusion is split by the canonical lower-face projection. -/
@[reassoc, stacks 017U "lower-face inclusion projection identity",
  stacks 017V "lower-face inclusion projection identity"]
theorem inclusion_comp_projection (U : SimplicialObject A) (n : ℕ) :
    (subobject U n).arrow ≫ projection U n = 𝟙 _ := sorry

/-- Canonical lower-face projections are natural in the simplicial object. -/
@[stacks 017U "lower-face projection naturality",
  stacks 017V "lower-face projection naturality"]
theorem projection_naturality {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    f.app (op ⦋n⦌) ≫ projection V n =
      projection U n ≫ subobject.map f n := sorry

/-- The generic coproduct source of the canonical splitting is the lower-face source. -/
@[stacks 017U "generic source of the lower-face splitting",
  stacks 017V "generic source of the lower-face splitting"]
theorem source_eq (U : SimplicialObject A) (Δ : SimplexCategoryᵒᵖ) :
    Split.source (Split.mk' (splitting U)) Δ = normalizedMoore.lowerFace.source U Δ := sorry

/-- The generic decomposition comparison specializes to the lower-face decomposition map. -/
@[stacks 017U "generic decomposition of the lower-face splitting",
  stacks 017V "generic decomposition of the lower-face splitting"]
theorem decomposition_eq (U : SimplicialObject A) (Δ : SimplexCategoryᵒᵖ) :
    Split.decomposition (Split.mk' (splitting U)) Δ =
      normalizedMoore.lowerFace.decomposition U Δ := sorry

namespace map

/-- The map on lower-face normalized summands commutes with their inclusions. -/
@[stacks 017U "lower-face splitting morphism compatibility",
  stacks 017V "lower-face splitting morphism compatibility"]
theorem comm {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    (splitting U).ι n ≫ f.app (op ⦋n⦌) =
      subobject.map f n ≫ (splitting V).ι n := sorry

end map

/-- A simplicial morphism as a morphism between the canonical lower-face splittings. -/
@[stacks 017U "functorial lower-face splitting morphism",
  stacks 017V "functorial lower-face splitting morphism"]
noncomputable def map {U V : SimplicialObject A} (f : U ⟶ V) :
    Split.mk' (splitting U) ⟶ Split.mk' (splitting V) where
  F := f
  f n := subobject.map f n
  comm n := map.comm f n

namespace map

/-- The underlying simplicial morphism of a lower-face splitting map is the original map. -/
@[simp, stacks 017U "underlying lower-face splitting morphism",
  stacks 017V "underlying lower-face splitting morphism"]
theorem underlying {U V : SimplicialObject A} (f : U ⟶ V) :
    (map f).F = f := sorry

/-- The distinguished-summand component of a lower-face splitting map is the induced subobject
map. -/
@[simp, stacks 017U "lower-face splitting morphism component",
  stacks 017V "lower-face splitting morphism component"]
theorem summand {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    (map f).f n = subobject.map f n := sorry

/-- The identity simplicial morphism induces the identity lower-face splitting morphism. -/
@[simp, stacks 017U "lower-face splitting identity",
  stacks 017V "lower-face splitting identity"]
theorem id (U : SimplicialObject A) :
    map (𝟙 U) = 𝟙 (Split.mk' (splitting U)) := sorry

/-- Lower-face splitting morphisms preserve composition. -/
@[stacks 017U "lower-face splitting composition",
  stacks 017V "lower-face splitting composition"]
theorem comp {U V W : SimplicialObject A} (f : U ⟶ V) (g : V ⟶ W) :
    map (f ≫ g) = map f ≫ map g := sorry

end map

/-- The functor from simplicial objects to their canonical lower-face splittings. -/
@[stacks 017U "functorial lower-face splitting",
  stacks 017V "functorial lower-face splitting"]
noncomputable def functor : SimplicialObject A ⥤ Split A where
  obj U := Split.mk' (splitting U)
  map f := map f
  map_id U := map.id U
  map_comp f g := map.comp f g

/-- The underlying simplicial object of the functorial lower-face splitting is unchanged. -/
@[simp, stacks 017U "underlying object of the lower-face splitting functor",
  stacks 017V "underlying object of the lower-face splitting functor"]
theorem functor.obj.underlying (U : SimplicialObject A) :
    ((functor (A := A)).obj U).X = U := sorry

/-- The distinguished summand of the functorial lower-face splitting is the lower-face
normalized Moore subobject. -/
@[simp, stacks 017U "summand of the lower-face splitting functor",
  stacks 017V "summand of the lower-face splitting functor"]
theorem functor.obj.summand (U : SimplicialObject A) (n : ℕ) :
    ((functor (A := A)).obj U).s.N n = (subobject U n : A) := sorry

/-- The distinguished inclusion of the functorial lower-face splitting is the lower-face
subobject inclusion. -/
@[simp, stacks 017U "inclusion of the lower-face splitting functor",
  stacks 017V "inclusion of the lower-face splitting functor"]
theorem functor.obj.inclusion (U : SimplicialObject A) (n : ℕ) :
    ((functor (A := A)).obj U).s.ι n = (subobject U n).arrow := sorry

/-- The underlying simplicial morphism of the functorial lower-face splitting is unchanged. -/
@[simp, stacks 017U "underlying map of the lower-face splitting functor",
  stacks 017V "underlying map of the lower-face splitting functor"]
theorem functor.map.underlying {U V : SimplicialObject A} (f : U ⟶ V) :
    ((functor (A := A)).map f).F = f := sorry

/-- The distinguished-summand component of the lower-face splitting functor map is the
induced lower-face subobject map. -/
@[simp, stacks 017U "component of the lower-face splitting functor map",
  stacks 017V "component of the lower-face splitting functor map"]
theorem functor.map.summand {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    ((functor (A := A)).map f).f n = subobject.map f n := sorry

end splitting

end normalizedMoore.lowerFace

end CategoryTheory.SimplicialObject
