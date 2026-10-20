module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bundled epi and mono simplex morphisms

This file owns the coefficient-free indexing types of epimorphisms and monomorphisms in the
simplex category.  They are independent of any skeleton, coskeleton, or additive coefficient
category, so combinatorial consumers can import them without importing Kan extensions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace SimplexCategory

/-- Epimorphisms between two fixed objects of the simplex category. -/
@[stacks 0190 "epic simplex morphisms"]
abbrev EpiHom (X Y : SimplexCategory) := { f : X ⟶ Y // Epi f }

namespace EpiHom

/-- The underlying simplex morphism of a bundled epimorphism. -/
@[stacks 0190 "underlying epic simplex morphism"]
abbrev hom {X Y : SimplexCategory} (f : EpiHom X Y) : X ⟶ Y := f.1

/-- The underlying morphism of an `EpiHom` is an epimorphism. -/
@[stacks 0190 "epic simplex morphism instance"]
instance epi {X Y : SimplexCategory} (f : EpiHom X Y) : Epi f.hom := f.2

/-- Reverse an epic simplex morphism along the covariant simplex involution. -/
@[stacks 0192 "reversal of an epic simplex morphism"]
def rev {X Y : SimplexCategory} (f : EpiHom X Y) : EpiHom X Y :=
  ⟨SimplexCategory.rev.map f.hom, Functor.map_epi SimplexCategory.rev f.hom⟩

/-- The underlying map of a reversed epic simplex morphism. -/
@[simp, stacks 0192 "underlying map of a reversed epic simplex morphism"]
theorem rev_hom {X Y : SimplexCategory} (f : EpiHom X Y) :
    (rev f).hom = SimplexCategory.rev.map f.hom := sorry

/-- Reversing an epic simplex morphism twice recovers the original one. -/
@[simp, stacks 0192 "involutivity of epic simplex-morphism reversal"]
theorem rev_rev {X Y : SimplexCategory} (f : EpiHom X Y) :
    rev (rev f) = f := sorry

/-- Reversal of epic simplex morphisms as an involutive equivalence. -/
@[stacks 0192 "equivalence of epic simplex morphisms under reversal"]
def revEquiv {X Y : SimplexCategory} : EpiHom X Y ≃ EpiHom X Y where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev

/-- Epic simplex morphisms between fixed endpoints form a finite type. -/
@[stacks 0190 "finiteness of epic simplex morphisms"]
noncomputable instance fintype (X Y : SimplexCategory) : Fintype (EpiHom X Y) :=
  Fintype.ofFinite _

/-- Precompose a bundled epimorphism when the composite is still epic. -/
@[stacks 0190 "partial precomposition of epic simplex morphisms"]
noncomputable def precomp {X Y Z : SimplexCategory} (a : EpiHom Y Z)
    (f : X ⟶ Y) : Option (EpiHom X Z) :=
  @dite _ (Epi (f ≫ a.hom)) (Classical.propDecidable _)
    (fun h ↦ some ⟨f ≫ a.hom, h⟩) (fun _ ↦ none)

/-- Partial epic precomposition returns `b` exactly when its underlying composite is `b.hom`. -/
@[simp, stacks 0190 "successful partial precomposition of epic simplex morphisms"]
theorem precomp.eq_some_iff {X Y Z : SimplexCategory} (a : EpiHom Y Z)
    (f : X ⟶ Y) (b : EpiHom X Z) :
    a.precomp f = some b ↔ f ≫ a.hom = b.hom := sorry

/-- Partial epic precomposition fails exactly when the underlying composite is not epic. -/
@[simp, stacks 0190 "failed partial precomposition of epic simplex morphisms"]
theorem precomp.eq_none_iff {X Y Z : SimplexCategory} (a : EpiHom Y Z)
    (f : X ⟶ Y) :
    a.precomp f = none ↔ ¬ Epi (f ≫ a.hom) := sorry

/-- An explicit epic proof computes partial precomposition to the corresponding bundled map. -/
@[simp, stacks 0190 "partial epic precomposition with an explicit proof"]
theorem precomp.of_epi {X Y Z : SimplexCategory} (a : EpiHom Y Z)
    (f : X ⟶ Y) (h : Epi (f ≫ a.hom)) :
    a.precomp f = some ⟨f ≫ a.hom, h⟩ := sorry

/-- A proof that the composite is not epic computes partial precomposition to `none`. -/
@[simp, stacks 0190 "partial epic precomposition of a nonepic composite"]
theorem precomp.of_not_epi {X Y Z : SimplexCategory} (a : EpiHom Y Z)
    (f : X ⟶ Y) (h : ¬ Epi (f ≫ a.hom)) :
    a.precomp f = none := sorry

/-- Precomposing a bundled epimorphism by an identity succeeds without changing it. -/
@[simp, stacks 0190 "identity law for partial epic precomposition"]
theorem precomp.id {X Y : SimplexCategory} (a : EpiHom X Y) :
    a.precomp (𝟙 X) = some a := sorry

/-- Successive partial precompositions agree with precomposition by the composite. -/
@[stacks 0190 "composition law for partial epic precomposition"]
theorem precomp.comp {W X Y Z : SimplexCategory} (a : EpiHom Y Z)
    (f : X ⟶ Y) (g : W ⟶ X) :
    (a.precomp f).bind (fun b ↦ b.precomp g) = a.precomp (g ≫ f) := sorry

end EpiHom

/-- Monomorphisms between two fixed objects of the simplex category. -/
@[stacks 0190 "monic simplex morphisms"]
abbrev MonoHom (X Y : SimplexCategory) := { f : X ⟶ Y // Mono f }

namespace MonoHom

/-- The underlying simplex morphism of a bundled monomorphism. -/
@[stacks 0190 "underlying monic simplex morphism"]
abbrev hom {X Y : SimplexCategory} (f : MonoHom X Y) : X ⟶ Y := f.1

/-- The underlying morphism of a `MonoHom` is a monomorphism. -/
@[stacks 0190 "monic simplex morphism instance"]
instance mono {X Y : SimplexCategory} (f : MonoHom X Y) : Mono f.hom := f.2

/-- Monic simplex morphisms between fixed endpoints form a finite type. -/
@[stacks 0190 "finiteness of monic simplex morphisms"]
noncomputable instance fintype (X Y : SimplexCategory) : Fintype (MonoHom X Y) :=
  Fintype.ofFinite _

/-- Postcompose a bundled monomorphism when the composite is still monic. -/
@[stacks 0190 "partial postcomposition of monic simplex morphisms"]
noncomputable def postcomp {X Y Z : SimplexCategory} (b : MonoHom X Y)
    (f : Y ⟶ Z) : Option (MonoHom X Z) :=
  @dite _ (Mono (b.hom ≫ f)) (Classical.propDecidable _)
    (fun h ↦ some ⟨b.hom ≫ f, h⟩) (fun _ ↦ none)

/-- Partial monic postcomposition returns `c` exactly when its underlying composite is `c.hom`. -/
@[simp, stacks 0190 "successful partial postcomposition of monic simplex morphisms"]
theorem postcomp.eq_some_iff {X Y Z : SimplexCategory} (b : MonoHom X Y)
    (f : Y ⟶ Z) (c : MonoHom X Z) :
    b.postcomp f = some c ↔ b.hom ≫ f = c.hom := sorry

/-- Partial monic postcomposition fails exactly when the underlying composite is not monic. -/
@[simp, stacks 0190 "failed partial postcomposition of monic simplex morphisms"]
theorem postcomp.eq_none_iff {X Y Z : SimplexCategory} (b : MonoHom X Y)
    (f : Y ⟶ Z) :
    b.postcomp f = none ↔ ¬ Mono (b.hom ≫ f) := sorry

/-- An explicit monic proof computes partial postcomposition to the corresponding bundled map. -/
@[simp, stacks 0190 "partial monic postcomposition with an explicit proof"]
theorem postcomp.of_mono {X Y Z : SimplexCategory} (b : MonoHom X Y)
    (f : Y ⟶ Z) (h : Mono (b.hom ≫ f)) :
    b.postcomp f = some ⟨b.hom ≫ f, h⟩ := sorry

/-- A proof that the composite is not monic computes partial postcomposition to `none`. -/
@[simp, stacks 0190 "partial monic postcomposition of a nonmonic composite"]
theorem postcomp.of_not_mono {X Y Z : SimplexCategory} (b : MonoHom X Y)
    (f : Y ⟶ Z) (h : ¬ Mono (b.hom ≫ f)) :
    b.postcomp f = none := sorry

/-- Postcomposing a bundled monomorphism by an identity succeeds without changing it. -/
@[simp, stacks 0190 "identity law for partial monic postcomposition"]
theorem postcomp.id {X Y : SimplexCategory} (b : MonoHom X Y) :
    b.postcomp (𝟙 Y) = some b := sorry

/-- Successive partial postcompositions agree with postcomposition by the composite. -/
@[stacks 0190 "composition law for partial monic postcomposition"]
theorem postcomp.comp {W X Y Z : SimplexCategory} (b : MonoHom W X)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (b.postcomp f).bind (fun c ↦ c.postcomp g) = b.postcomp (f ≫ g) := sorry

end MonoHom

end SimplexCategory
