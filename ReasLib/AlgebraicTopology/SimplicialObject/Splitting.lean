/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Splittings and morphisms of split simplicial objects

This file separates arbitrary Mathlib splitting data from splittings whose distinguished maps
are genuine subobjects, then records property-transfer API for morphisms of split simplicial
objects whose values are types.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Splitting

variable {C : Type u} [Category.{v} C] {X : SimplicialObject C}

namespace IndexSet

variable {Δ : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ)

/-- Reverse the epimorphism indexing a splitting summand. Reversal fixes its source and target
simplex objects, so this is an endomorphism of the same splitting index type. -/
@[stacks 017U "reversal on splitting indices", stacks 017V "reversal on splitting indices"]
def rev : Splitting.IndexSet Δ :=
  ⟨A.1, ⟨SimplexCategory.rev.map A.e,
    Functor.map_epi SimplexCategory.rev A.e⟩⟩

/-- Reversal does not change the target simplex of a splitting index. -/
@[simp, stacks 017U "target of a reversed splitting index",
  stacks 017V "target of a reversed splitting index"]
theorem rev_fst : (rev A).1 = A.1 := sorry

/-- The epimorphism of a reversed splitting index is the reversed original epimorphism. -/
@[simp, stacks 017U "epimorphism of a reversed splitting index",
  stacks 017V "epimorphism of a reversed splitting index"]
theorem rev_e : (rev A).e = SimplexCategory.rev.map A.e := sorry

/-- Reversing a splitting index twice recovers the original index. -/
@[simp, stacks 017U "involutivity of splitting-index reversal",
  stacks 017V "involutivity of splitting-index reversal"]
theorem rev_rev : rev (rev A) = A := sorry

/-- Reversal preserves the distinguished identity splitting index. -/
@[simp, stacks 017U "identity criterion for a reversed splitting index",
  stacks 017V "identity criterion for a reversed splitting index"]
theorem rev_eqId : (rev A).EqId ↔ A.EqId := sorry

/-- Reversal of simplex epimorphisms as an equivalence of a splitting index type. -/
@[stacks 017U "equivalence of splitting indices under reversal",
  stacks 017V "equivalence of splitting indices under reversal"]
def revEquiv : Splitting.IndexSet Δ ≃ Splitting.IndexSet Δ where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev

end IndexSet

/-- A splitting is monic when every distinguished summand map is a monomorphism. This is the
additional condition needed to regard the summands as actual subobjects. -/
@[stacks 017P "monic splitting"]
class IsMonic (s : Splitting X) : Prop where
  /-- Every distinguished summand map is a monomorphism. -/
  mono (n : ℕ) : Mono (s.ι n)

attribute [instance] IsMonic.mono

/-- The degree-`n` subobject represented by a monic splitting. -/
@[stacks 017P "subobject represented by a splitting"]
def subobject (s : Splitting X) [s.IsMonic] (n : ℕ) :
    Subobject (X _⦋n⦌) :=
  Subobject.mk (s.ι n)

end CategoryTheory.SimplicialObject.Splitting

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- A simplicial object is split in the source sense when it has a splitting whose distinguished
maps represent subobjects. -/
@[stacks 017P "existence of a splitting by subobjects"]
def IsSplit (X : SimplicialObject C) : Prop :=
  ∃ s : Splitting X, s.IsMonic

namespace Splitting

/-- A chosen monic splitting witnesses splitness of the underlying simplicial object. -/
@[stacks 017P "chosen monic splitting witnesses splitness"]
theorem isSplit {X : SimplicialObject C} (s : Splitting X) [s.IsMonic] :
    IsSplit X := sorry

/-- A chosen splitting witnesses splitness when monicity is supplied as an ordinary proof.

This proof-form companion avoids requiring downstream users to install a temporary instance for
an already established splitting property. -/
@[stacks 017P "splitness from an explicit monic splitting proof"]
theorem isSplit_of_monic {X : SimplicialObject C} (s : Splitting X)
    (hs : s.IsMonic) : IsSplit X := sorry

end Splitting

end CategoryTheory.SimplicialObject

namespace CategoryTheory.SimplicialObject.Split

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]

/-- The coproduct of the distinguished summands of a split simplicial object in degree `Δ`. -/
@[stacks 017P "coproduct source of a split simplicial object"]
noncomputable abbrev source (S : Split C) (Δ : SimplexCategoryᵒᵖ) : C :=
  ∐ Splitting.summand S.s.N Δ

namespace source

/-- The map between coproduct sources induced by a morphism of split simplicial objects. -/
@[stacks 017P "map on coproduct sources of split simplicial objects"]
noncomputable def map {S T : Split C} (f : S ⟶ T) (Δ : SimplexCategoryᵒᵖ) :
    source S Δ ⟶ source T Δ :=
  Limits.Sigma.map (fun a ↦ f.f a.1.unop.len)

/-- The source map commutes with each canonical coproduct inclusion. -/
@[reassoc, stacks 017P "coproduct source map inclusion formula"]
theorem ι_map {S T : Split C} (f : S ⟶ T) (Δ : SimplexCategoryᵒᵖ)
    (a : Splitting.IndexSet Δ) :
    Sigma.ι (Splitting.summand S.s.N Δ) a ≫ map f Δ =
      f.f a.1.unop.len ≫ Sigma.ι (Splitting.summand T.s.N Δ) a := sorry

/-- The identity of a split simplicial object induces the identity source map. -/
@[simp, stacks 017P "identity map on split coproduct sources"]
theorem map_id (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    map (𝟙 S) Δ = 𝟙 (source S Δ) := sorry

/-- Source maps preserve composition of morphisms of split simplicial objects. -/
@[stacks 017P "composition of maps on split coproduct sources"]
theorem map_comp {S T R : Split C} (f : S ⟶ T) (g : T ⟶ R)
    (Δ : SimplexCategoryᵒᵖ) :
    map (f ≫ g) Δ = map f Δ ≫ map g Δ := sorry

/-- Coproduct sources in a fixed degree form a functor on split simplicial objects. -/
@[stacks 017P "coproduct source functor of split simplicial objects"]
noncomputable def functor (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (Δ : SimplexCategoryᵒᵖ) : Split C ⥤ C where
  obj S := source S Δ
  map f := source.map f Δ
  map_id S := source.map_id S Δ
  map_comp f g := source.map_comp f g Δ

/-- The object formula for the coproduct source functor. -/
@[simp, stacks 017P "coproduct source functor object formula"]
theorem functor.obj (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    (functor C Δ).obj S = source S Δ := sorry

/-- The morphism formula for the coproduct source functor. -/
@[simp, stacks 017P "coproduct source functor map formula"]
theorem functor.map {S T : Split C} (f : S ⟶ T) (Δ : SimplexCategoryᵒᵖ) :
    (functor C Δ).map f = source.map f Δ := sorry

end source

/-- The canonical comparison from the coproduct source of a splitting to its underlying
simplicial object in degree `Δ`. -/
@[stacks 017P "decomposition map of a split simplicial object"]
noncomputable def decomposition (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    source S Δ ⟶ S.X.obj Δ :=
  Sigma.desc fun a ↦ (S.s.cofan Δ).inj a

namespace decomposition

/-- The decomposition comparison restricts to the prescribed splitting cofan on every
summand. -/
@[reassoc, stacks 017P "split decomposition summand formula"]
theorem ι (S : Split C) (Δ : SimplexCategoryᵒᵖ) (a : Splitting.IndexSet Δ) :
    Sigma.ι (Splitting.summand S.s.N Δ) a ≫ decomposition S Δ =
      (S.s.cofan Δ).inj a := sorry

/-- The decomposition comparison of a split simplicial object is an isomorphism. -/
@[stacks 017P "split decomposition isomorphism"]
instance isIso (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    IsIso (decomposition S Δ) := sorry

/-- The comparison isomorphism determined by the coproduct and splitting colimit cocones. -/
@[stacks 017P "split decomposition comparison isomorphism"]
noncomputable def iso (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    source S Δ ≅ S.X.obj Δ :=
  IsColimit.coconePointUniqueUpToIso
    (coproductIsCoproduct (Splitting.summand S.s.N Δ)) (S.s.isColimit Δ)

/-- The forward map of the comparison isomorphism is the canonical decomposition map. -/
@[simp, stacks 017P "split decomposition comparison forward map"]
theorem iso_hom (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    (iso S Δ).hom = decomposition S Δ := sorry

/-- Naturality of the coproduct-to-object comparison isomorphism. -/
@[stacks 017P "naturality of the split decomposition comparison isomorphism"]
theorem iso_naturality {S T : Split C} (f : S ⟶ T) (Δ : SimplexCategoryᵒᵖ) :
    source.map f Δ ≫ (iso T Δ).hom = (iso S Δ).hom ≫ f.F.app Δ := sorry

/-- The inverse of the split decomposition comparison. -/
@[stacks 017P "inverse of the split decomposition"]
noncomputable def inv (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    S.X.obj Δ ⟶ source S Δ :=
  (iso S Δ).inv

/-- The split decomposition followed by its inverse is the identity on the source. -/
@[reassoc, stacks 017P "split decomposition hom-inverse law"]
theorem hom_inv_id (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    decomposition S Δ ≫ inv S Δ = 𝟙 (source S Δ) := sorry

/-- The inverse split decomposition followed by the decomposition is the identity on simplices. -/
@[reassoc, stacks 017P "split decomposition inverse-hom law"]
theorem inv_hom_id (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    inv S Δ ≫ decomposition S Δ = 𝟙 (S.X.obj Δ) := sorry

/-- The decomposition comparison is natural in morphisms of split simplicial objects. -/
@[stacks 017P "naturality of split decomposition"]
theorem naturality {S T : Split C} (f : S ⟶ T) (Δ : SimplexCategoryᵒᵖ) :
    source.map f Δ ≫ decomposition T Δ =
      decomposition S Δ ≫ f.F.app Δ := sorry

/-- The degreewise decomposition comparisons form a natural transformation. -/
@[stacks 017P "split decomposition natural transformation"]
noncomputable def natTrans (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (Δ : SimplexCategoryᵒᵖ) :
    source.functor C Δ ⟶ Split.forget C ⋙ (evaluation SimplexCategoryᵒᵖ C).obj Δ where
  app S := decomposition S Δ
  naturality _ _ f := decomposition.naturality f Δ

/-- The component formula for the split decomposition natural transformation. -/
@[simp, stacks 017P "split decomposition natural transformation component"]
theorem natTrans.app (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    (natTrans C Δ).app S = decomposition S Δ := sorry

/-- The split decomposition natural transformation is an isomorphism. -/
@[stacks 017P "split decomposition natural isomorphism instance"]
instance natTrans.isIso (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (Δ : SimplexCategoryᵒᵖ) : IsIso (natTrans C Δ) := sorry

/-- The canonical decomposition of split simplicial objects as a natural isomorphism in a
fixed simplicial degree. -/
@[stacks 017P "split decomposition natural isomorphism"]
noncomputable def natIso (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (Δ : SimplexCategoryᵒᵖ) :
    source.functor C Δ ≅ Split.forget C ⋙ (evaluation SimplexCategoryᵒᵖ C).obj Δ :=
  NatIso.ofComponents (fun S ↦ iso S Δ)
    (fun f ↦ iso_naturality f Δ)

/-- The forward map of the split decomposition natural isomorphism. -/
@[simp, stacks 017P "split decomposition natural isomorphism forward map"]
theorem natIso.hom (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (Δ : SimplexCategoryᵒᵖ) :
    (natIso C Δ).hom = natTrans C Δ := sorry

/-- The component of the split decomposition natural isomorphism has the canonical comparison
as its forward map. -/
@[simp, stacks 017P "split decomposition natural isomorphism component forward map"]
theorem natIso.hom_app (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    (natIso C Δ).hom.app S = decomposition S Δ := sorry

/-- The component of the split decomposition natural isomorphism has the canonical inverse map. -/
@[simp, stacks 017P "split decomposition natural isomorphism component inverse map"]
theorem natIso.inv_app (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (S : Split C) (Δ : SimplexCategoryᵒᵖ) :
    (natIso C Δ).inv.app S = inv S Δ := sorry

end decomposition

namespace Hom

/-- A morphism of split simplicial objects in types that is injective on the distinguished
summands through degree `n` is injective in degree `n`. -/
@[stacks 017S "injectivity for morphisms of split simplicial objects"]
theorem app_injective {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂)
    (n : ℕ) (hΦ : ∀ m : ℕ, m ≤ n → Function.Injective (Φ.f m)) :
    Function.Injective (Φ.F.app (op ⦋n⦌)) := sorry

/-- Injectivity of a morphism of split simplicial objects in degree `n` is equivalent to
injectivity on all distinguished summands through degree `n`. -/
@[stacks 017S "injectivity detected on split summands"]
theorem app_injective_iff {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂) (n : ℕ) :
    Function.Injective (Φ.F.app (op ⦋n⦌)) ↔
      ∀ m : ℕ, m ≤ n → Function.Injective (Φ.f m) := sorry

/-- A morphism of split simplicial objects in types that is surjective on the distinguished
summands through degree `n` is surjective in degree `n`. -/
@[stacks 017S "surjectivity for morphisms of split simplicial objects"]
theorem app_surjective {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂)
    (n : ℕ) (hΦ : ∀ m : ℕ, m ≤ n → Function.Surjective (Φ.f m)) :
    Function.Surjective (Φ.F.app (op ⦋n⦌)) := sorry

/-- Surjectivity of a morphism of split simplicial objects in degree `n` is equivalent to
surjectivity on all distinguished summands through degree `n`. -/
@[stacks 017S "surjectivity detected on split summands"]
theorem app_surjective_iff {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂) (n : ℕ) :
    Function.Surjective (Φ.F.app (op ⦋n⦌)) ↔
      ∀ m : ℕ, m ≤ n → Function.Surjective (Φ.f m) := sorry

/-- A morphism of split simplicial objects in types that is bijective on the distinguished
summands through degree `n` is bijective in degree `n`. -/
@[stacks 017S "bijectivity for morphisms of split simplicial objects"]
theorem app_bijective {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂)
    (n : ℕ) (hΦ : ∀ m : ℕ, m ≤ n → Function.Bijective (Φ.f m)) :
    Function.Bijective (Φ.F.app (op ⦋n⦌)) := sorry

/-- Bijectivity of a morphism of split simplicial objects in degree `n` is equivalent to
bijectivity on all distinguished summands through degree `n`. -/
@[stacks 017S "bijectivity detected on split summands"]
theorem app_bijective_iff {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂) (n : ℕ) :
    Function.Bijective (Φ.F.app (op ⦋n⦌)) ↔
      ∀ m : ℕ, m ≤ n → Function.Bijective (Φ.f m) := sorry

end Hom

end CategoryTheory.SimplicialObject.Split
