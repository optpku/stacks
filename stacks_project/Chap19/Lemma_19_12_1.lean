module

public import ReasLib.CategoryTheory.Abelian.SeparatorCoproduct.Refinement.Grothendieck
import StacksCheckRecall

@[expose] public section

/-!
# Small Epi Refinements

The reusable construction for Lemma 19.12.1 is owned by `CategoryTheory.SeparatorEpi`.  This file
records only the tagged source specialization and checks the principal construction API.
-/

open CategoryTheory

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {U M N : C}

/- Lemma 19.12.1: an epimorphism admits a subobject of its source which still maps epimorphically
to the target and has subobject cardinal at most `c(|N|)`, computed using the chosen separator
`U`. -/
@[stacks 079J] #check
  fun (hU : IsSeparator U) (π : M ⟶ N) [Epi π] ↦
    (SeparatorEpi.Grothendieck.exists_refinement
      hU π :
      ∃ P : Subobject M,
        Epi (P.arrow ≫ π) ∧
          Cardinal.mk (Subobject (P : C)) ≤
            Subobject.coproductCardinal U (Subobject.smallCardinal N))

/- The concrete reusable owner exposes the component family, coproduct map, image refinement and
map from the refinement to the target. -/
#check @SeparatorEpi.Family
#check @SeparatorEpi.Family.map
#check @SeparatorEpi.Family.refinement
#check @SeparatorEpi.Family.toTarget
#check @SeparatorEpi.Family.epi_toTarget
#check @SeparatorEpi.Family.cardinalMk_refinement_le
#check @Subobject.coproductCardinal
#check @Subobject.coproductCardinal_mono

end CategoryTheory
