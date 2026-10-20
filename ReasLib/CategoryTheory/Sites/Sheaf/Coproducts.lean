module

public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable {C : Type u} [Category.{u} C] [HasInitial C]
variable {J : GrothendieckTopology C}
variable {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
variable {I : C}
variable {α : Type u} {X : α → C}

namespace CategoryTheory.Presieve

/-- A sheaf sends a disjoint coproduct family to the product of its sections. -/
theorem isIso_sectionsToProduct_of_isSheaf
    (hI : IsInitial I)
    (c : Cofan X) (hc : IsColimit c)
    [hpair : (Presieve.ofArrows X c.inj).HasPairwisePullbacks]
    [hmono : ∀ i, Mono (c.inj i)]
    (hF : Presheaf.IsSheaf J F)
    (hcover : Sieve.generate (Presieve.ofArrows X c.inj) ∈ J c.pt)
    (hempty : Sieve.generate (⊥ : Presieve I) ∈ J I)
    (hd : Pairwise fun i j ↦
      IsPullback (initial.to (X i)) (initial.to (X j)) (c.inj i) (c.inj j)) :
    IsIso (Pi.lift (fun i ↦ F.map (c.inj i).op)) := sorry

end CategoryTheory.Presieve
