/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans

/-!
# Precomposition of modifications

The pointwise action of a fixed pseudofunctor on modifications between strong
transformations. The functor-bicategory hom action is in
`Precomposition.Hom`.
-/

@[expose] public section

universe wA vA uA wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Precomposition

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped Pseudofunctor.StrongTrans

variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace StrongTrans

variable {F G H : Pseudofunctor B D}

namespace Modification

variable {η θ ι : StrongTrans F G}

/-- Naturality for precomposition of a modification. -/
private theorem precomp_naturality_coherence
    (Γ : Modification η θ) (K : Pseudofunctor A B) :
    ∀ {a b : A} (f : a ⟶ b),
      (K.comp F).map f ◁ Γ.app (K.obj b) ≫
          (θ.naturality (K.map f)).hom =
        (η.naturality (K.map f)).hom ≫
          Γ.app (K.obj a) ▷ (K.comp G).map f := sorry

/-- Precompose a modification by a pseudofunctor. -/
def precomp (Γ : Modification η θ) (K : Pseudofunctor A B) :
    Modification (η.precomp K) (θ.precomp K) where
  app a := Γ.app (K.obj a)
  naturality := precomp_naturality_coherence Γ K

/-- Components of a precomposed modification are evaluated at the image object. -/
@[simp]
theorem precomp.app
    (Γ : Modification η θ) (K : Pseudofunctor A B) (a : A) :
    (Γ.precomp K).app a = Γ.app (K.obj a) := sorry

/-- Naturality of a precomposed modification is evaluated at the image `1`-morphism. -/
@[simp]
theorem precomp.naturality
    (Γ : Modification η θ) (K : Pseudofunctor A B)
    {a b : A} (f : a ⟶ b) :
    (Γ.precomp K).naturality f = Γ.naturality (K.map f) := sorry

/-- Precomposition preserves identity modifications. -/
@[simp]
theorem precomp.id
    (η : StrongTrans F G) (K : Pseudofunctor A B) :
    (Modification.id η).precomp K =
      Modification.id (η.precomp K) := sorry

/-- Precomposition preserves vertical composition of modifications. -/
@[simp]
theorem precomp.vcomp
    (Γ : Modification η θ) (Δ : Modification θ ι)
    (K : Pseudofunctor A B) :
    (Modification.vcomp Γ Δ).precomp K =
      Modification.vcomp (Γ.precomp K) (Δ.precomp K) := sorry

end Modification

end StrongTrans

end Precomposition

end Pseudofunctor

end CategoryTheory
