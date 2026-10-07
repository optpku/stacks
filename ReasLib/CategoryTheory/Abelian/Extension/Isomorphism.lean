module

public import ReasLib.CategoryTheory.Abelian.Extension.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Isomorphism Classes of Fixed-Endpoint Extensions

The extension category supplies the relevant notion of isomorphism.  This
module therefore uses Mathlib's canonical `IsIsomorphic` setoid rather than a
parallel endpoint-isomorphism relation.
-/

namespace CategoryTheory

universe v u

open Limits

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {A B : C}

namespace Extension

/-- Presentation view of an isomorphism of fixed-endpoint extensions: an
isomorphism of middle objects satisfying the two endpoint equations.

The category-theoretic owner is `IsIsomorphic S T`; this view is retained for
constructing and eliminating extension isomorphisms componentwise. -/
def Isomorphic (S T : Extension A B) : Prop :=
  ∃ e : S.E ≅ T.E, S.f ≫ e.hom = T.f ∧ e.hom ≫ T.g = S.g

/-- The componentwise presentation of an extension isomorphism is equivalent
to Mathlib's canonical categorical notion. -/
theorem isomorphic_iff_isIsomorphic {S T : Extension A B} :
    Isomorphic S T ↔ IsIsomorphic S T := sorry

end Extension

/-- Definition 12.6.2: the isomorphism classes of extensions of `B` by `A`.

The canonical derived-category owner of the resulting degree-one extension
group is `Abelian.Ext B A 1`. -/
@[stacks 010K]
abbrev ExtensionClass (A B : C) :=
  _root_.Quotient (isIsomorphicSetoid (Extension A B))

namespace ExtensionClass

/-- Categorically isomorphic fixed-endpoint extensions determine the same
extension class. -/
theorem mk_eq_mk_of_isIsomorphic {S T : Extension A B} (h : IsIsomorphic S T) :
    (⟦S⟧ : ExtensionClass A B) = ⟦T⟧ := sorry

/-- A componentwise middle-object isomorphism determines equality of extension
classes through the canonical categorical quotient. -/
theorem mk_eq_mk_of_isomorphic {S T : Extension A B} (h : Extension.Isomorphic S T) :
    (⟦S⟧ : ExtensionClass A B) = ⟦T⟧ := sorry

end ExtensionClass

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : C}

namespace Extension

/-- Every endpoint-preserving morphism between fixed-endpoint short exact extensions is an
isomorphism on middle objects. -/
@[stacks 010J "fixed-endpoint short five lemma"]
instance Hom.isIso {S T : Extension A B} (f : S ⟶ T) : IsIso f.hom := sorry

/-- Fixed-endpoint extensions are categorically isomorphic exactly when there is a morphism
between them. -/
@[stacks 010K "isomorphism from an extension morphism"]
theorem isIsomorphic_iff_nonempty_hom {S T : Extension A B} :
    IsIsomorphic S T ↔ Nonempty (S ⟶ T) := sorry

end Extension

namespace ExtensionClass

/-- Any morphism between fixed-endpoint extensions identifies their extension classes. -/
@[stacks 010K "extension-class equality from an extension morphism"]
theorem mk_eq_mk_of_hom {S T : Extension A B} (f : S ⟶ T) :
    (⟦S⟧ : ExtensionClass A B) = ⟦T⟧ := sorry

end ExtensionClass

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : C} {S T : Extension A B}
variable (f : S ⟶ T)

#synth IsIso f.hom

end

end CategoryTheory
