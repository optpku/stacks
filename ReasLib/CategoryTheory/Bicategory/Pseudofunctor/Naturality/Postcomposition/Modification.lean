module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.StrongTrans

/-!
# Postcomposition of modifications

The pointwise action of a fixed pseudofunctor on modifications between strong
transformations. The functor-bicategory hom action is in
`Postcomposition.Hom`.
-/

@[expose] public section

universe wA vA uA wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Postcomposition

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped Pseudofunctor.StrongTrans

variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace StrongTrans

variable {F G H : Pseudofunctor A B}

namespace Modification

variable {η θ ι : StrongTrans F G}

/-- Naturality for postcomposition of a modification. -/
private theorem postcomp_naturality_coherence
    (Γ : Modification η θ) (K : Pseudofunctor B D) :
    ∀ {a b : A} (f : a ⟶ b),
      (F.comp K).map f ◁ K.map₂ (Γ.app b) ≫
          ((θ.postcomp K).naturality f).hom =
        ((η.postcomp K).naturality f).hom ≫
          K.map₂ (Γ.app a) ▷ (G.comp K).map f := sorry

/-- Postcompose a modification by a pseudofunctor. -/
def postcomp (Γ : Modification η θ) (K : Pseudofunctor B D) :
    Modification (η.postcomp K) (θ.postcomp K) where
  app a := K.map₂ (Γ.app a)
  naturality := postcomp_naturality_coherence Γ K

/-- Components of a postcomposed modification are images of the original components. -/
@[simp]
theorem postcomp.app
    (Γ : Modification η θ) (K : Pseudofunctor B D) (a : A) :
    (Γ.postcomp K).app a = K.map₂ (Γ.app a) := sorry

/-- Naturality of a postcomposed modification is the mapped naturality square. -/
@[simp]
theorem postcomp.naturality
    (Γ : Modification η θ) (K : Pseudofunctor B D)
    {a b : A} (f : a ⟶ b) :
    (Γ.postcomp K).naturality f =
      postcomp_naturality_coherence Γ K f := sorry

/-- Postcomposition preserves identity modifications. -/
@[simp]
theorem postcomp.id
    (η : StrongTrans F G) (K : Pseudofunctor B D) :
    (Modification.id η).postcomp K =
      Modification.id (η.postcomp K) := sorry

/-- Postcomposition preserves vertical composition of modifications. -/
@[simp]
theorem postcomp.vcomp
    (Γ : Modification η θ) (Δ : Modification θ ι)
    (K : Pseudofunctor B D) :
    (Modification.vcomp Γ Δ).postcomp K =
      Modification.vcomp (Γ.postcomp K) (Δ.postcomp K) := sorry

end Modification

end StrongTrans

end Postcomposition

end Pseudofunctor

end CategoryTheory
